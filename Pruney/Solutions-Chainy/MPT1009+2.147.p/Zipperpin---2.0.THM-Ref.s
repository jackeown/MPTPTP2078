%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1GIpr7dG6m

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:10 EST 2020

% Result     : Theorem 4.71s
% Output     : Refutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 392 expanded)
%              Number of leaves         :   57 ( 142 expanded)
%              Depth                    :   13
%              Number of atoms          : 1075 (5197 expanded)
%              Number of equality atoms :   79 ( 292 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X81: $i,X82: $i,X83: $i] :
      ( ~ ( v1_funct_2 @ X83 @ X81 @ X82 )
      | ( X81
        = ( k1_relset_1 @ X81 @ X82 @ X83 ) )
      | ~ ( zip_tseitin_2 @ X83 @ X82 @ X81 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('4',plain,(
    ! [X79: $i,X80: $i] :
      ( ( zip_tseitin_1 @ X79 @ X80 )
      | ( X79 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X84: $i,X85: $i,X86: $i] :
      ( ~ ( zip_tseitin_1 @ X84 @ X85 )
      | ( zip_tseitin_2 @ X86 @ X84 @ X85 )
      | ~ ( m1_subset_1 @ X86 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X85 @ X84 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_2 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_2 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( ( k1_relset_1 @ X63 @ X64 @ X62 )
        = ( k1_relat_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) )
      | ( ( k7_relset_1 @ X69 @ X70 @ X68 @ X71 )
        = ( k9_relat_1 @ X68 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      | ( r2_hidden @ X38 @ X44 )
      | ( X44
       != ( k3_enumset1 @ X43 @ X42 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('28',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X38 @ ( k3_enumset1 @ X43 @ X42 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X32 != X31 )
      | ~ ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('31',plain,(
    ! [X31: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X31 @ X33 @ X34 @ X35 @ X36 @ X31 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( r2_hidden @ X56 @ ( k1_relat_1 @ X57 ) )
      | ( ( k11_relat_1 @ X57 @ X56 )
        = ( k1_tarski @ ( k1_funct_1 @ X57 @ X56 ) ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( v1_relat_1 @ X50 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X54: $i,X55: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('46',plain,(
    ! [X76: $i,X77: $i,X78: $i] :
      ( ( ( k7_relset_1 @ X76 @ X77 @ X78 @ X76 )
        = ( k2_relset_1 @ X76 @ X77 @ X78 ) )
      | ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X76 @ X77 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('47',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( ( k2_relset_1 @ X66 @ X67 @ X65 )
        = ( k2_relat_1 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('51',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('53',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48','53'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('56',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('58',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('59',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k11_relat_1 @ X52 @ X53 )
        = ( k9_relat_1 @ X52 @ ( k1_tarski @ X53 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['54','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','43','44','64'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('69',plain,(
    ! [X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X72 ) @ X73 )
      | ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X74 @ X73 ) ) )
      | ~ ( m1_subset_1 @ X72 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X74 @ X75 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('72',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X59 @ X60 @ X58 @ X61 ) @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('75',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) )
      | ( ( k7_relset_1 @ X69 @ X70 @ X68 @ X71 )
        = ( k9_relat_1 @ X68 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('78',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['21','65','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1GIpr7dG6m
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.20/0.33  % DateTime   : Tue Dec  1 16:12:34 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 4.71/4.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.71/4.95  % Solved by: fo/fo7.sh
% 4.71/4.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.71/4.95  % done 1521 iterations in 4.503s
% 4.71/4.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.71/4.95  % SZS output start Refutation
% 4.71/4.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.71/4.95  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.71/4.95  thf(sk_D_type, type, sk_D: $i).
% 4.71/4.95  thf(sk_A_type, type, sk_A: $i).
% 4.71/4.95  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.71/4.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.71/4.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.71/4.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.71/4.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.71/4.95  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 4.71/4.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.71/4.95  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.71/4.95  thf(sk_B_type, type, sk_B: $i).
% 4.71/4.95  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 4.71/4.95  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 4.71/4.95  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.71/4.95  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 4.71/4.95  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.71/4.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.71/4.95  thf(sk_C_type, type, sk_C: $i).
% 4.71/4.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.71/4.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 4.71/4.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.71/4.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.71/4.95  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 4.71/4.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.71/4.95  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 4.71/4.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.71/4.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 4.71/4.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.71/4.95  thf(t64_funct_2, conjecture,
% 4.71/4.95    (![A:$i,B:$i,C:$i,D:$i]:
% 4.71/4.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 4.71/4.95         ( m1_subset_1 @
% 4.71/4.95           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 4.71/4.95       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 4.71/4.95         ( r1_tarski @
% 4.71/4.95           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 4.71/4.95           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 4.71/4.95  thf(zf_stmt_0, negated_conjecture,
% 4.71/4.95    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.71/4.95        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 4.71/4.95            ( m1_subset_1 @
% 4.71/4.95              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 4.71/4.95          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 4.71/4.95            ( r1_tarski @
% 4.71/4.95              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 4.71/4.95              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 4.71/4.95    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 4.71/4.95  thf('0', plain,
% 4.71/4.95      (~ (r1_tarski @ 
% 4.71/4.95          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 4.71/4.95          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf(d1_funct_2, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.71/4.95       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.71/4.95           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.71/4.95             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.71/4.95         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.71/4.95           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.71/4.95             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.71/4.95  thf(zf_stmt_1, axiom,
% 4.71/4.95    (![C:$i,B:$i,A:$i]:
% 4.71/4.95     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 4.71/4.95       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.71/4.95  thf('2', plain,
% 4.71/4.95      (![X81 : $i, X82 : $i, X83 : $i]:
% 4.71/4.95         (~ (v1_funct_2 @ X83 @ X81 @ X82)
% 4.71/4.95          | ((X81) = (k1_relset_1 @ X81 @ X82 @ X83))
% 4.71/4.95          | ~ (zip_tseitin_2 @ X83 @ X82 @ X81))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.71/4.95  thf('3', plain,
% 4.71/4.95      ((~ (zip_tseitin_2 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 4.71/4.95        | ((k1_tarski @ sk_A)
% 4.71/4.95            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 4.71/4.95      inference('sup-', [status(thm)], ['1', '2'])).
% 4.71/4.95  thf(zf_stmt_2, axiom,
% 4.71/4.95    (![B:$i,A:$i]:
% 4.71/4.95     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.71/4.95       ( zip_tseitin_1 @ B @ A ) ))).
% 4.71/4.95  thf('4', plain,
% 4.71/4.95      (![X79 : $i, X80 : $i]:
% 4.71/4.95         ((zip_tseitin_1 @ X79 @ X80) | ((X79) = (k1_xboole_0)))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.71/4.95  thf('5', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 4.71/4.95  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 4.71/4.95  thf(zf_stmt_5, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.71/4.95       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 4.71/4.95         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.71/4.95           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.71/4.95             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.71/4.95  thf('6', plain,
% 4.71/4.95      (![X84 : $i, X85 : $i, X86 : $i]:
% 4.71/4.95         (~ (zip_tseitin_1 @ X84 @ X85)
% 4.71/4.95          | (zip_tseitin_2 @ X86 @ X84 @ X85)
% 4.71/4.95          | ~ (m1_subset_1 @ X86 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X85 @ X84))))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.71/4.95  thf('7', plain,
% 4.71/4.95      (((zip_tseitin_2 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 4.71/4.95        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 4.71/4.95      inference('sup-', [status(thm)], ['5', '6'])).
% 4.71/4.95  thf('8', plain,
% 4.71/4.95      ((((sk_B) = (k1_xboole_0))
% 4.71/4.95        | (zip_tseitin_2 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 4.71/4.95      inference('sup-', [status(thm)], ['4', '7'])).
% 4.71/4.95  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf('10', plain, ((zip_tseitin_2 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 4.71/4.95      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 4.71/4.95  thf('11', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf(redefinition_k1_relset_1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.71/4.95       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.71/4.95  thf('12', plain,
% 4.71/4.95      (![X62 : $i, X63 : $i, X64 : $i]:
% 4.71/4.95         (((k1_relset_1 @ X63 @ X64 @ X62) = (k1_relat_1 @ X62))
% 4.71/4.95          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64))))),
% 4.71/4.95      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.71/4.95  thf('13', plain,
% 4.71/4.95      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.71/4.95      inference('sup-', [status(thm)], ['11', '12'])).
% 4.71/4.95  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 4.71/4.95      inference('demod', [status(thm)], ['3', '10', '13'])).
% 4.71/4.95  thf('15', plain,
% 4.71/4.95      (~ (r1_tarski @ 
% 4.71/4.95          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 4.71/4.95          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 4.71/4.95      inference('demod', [status(thm)], ['0', '14'])).
% 4.71/4.95  thf('16', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 4.71/4.95      inference('demod', [status(thm)], ['3', '10', '13'])).
% 4.71/4.95  thf('18', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 4.71/4.95      inference('demod', [status(thm)], ['16', '17'])).
% 4.71/4.95  thf(redefinition_k7_relset_1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i,D:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.71/4.95       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 4.71/4.95  thf('19', plain,
% 4.71/4.95      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i]:
% 4.71/4.95         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X70)))
% 4.71/4.95          | ((k7_relset_1 @ X69 @ X70 @ X68 @ X71) = (k9_relat_1 @ X68 @ X71)))),
% 4.71/4.95      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.71/4.95  thf('20', plain,
% 4.71/4.95      (![X0 : $i]:
% 4.71/4.95         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 4.71/4.95           = (k9_relat_1 @ sk_D @ X0))),
% 4.71/4.95      inference('sup-', [status(thm)], ['18', '19'])).
% 4.71/4.95  thf('21', plain,
% 4.71/4.95      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 4.71/4.95          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 4.71/4.95      inference('demod', [status(thm)], ['15', '20'])).
% 4.71/4.95  thf('22', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 4.71/4.95      inference('demod', [status(thm)], ['3', '10', '13'])).
% 4.71/4.95  thf(t69_enumset1, axiom,
% 4.71/4.95    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.71/4.95  thf('23', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 4.71/4.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.71/4.95  thf(t70_enumset1, axiom,
% 4.71/4.95    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.71/4.95  thf('24', plain,
% 4.71/4.95      (![X4 : $i, X5 : $i]:
% 4.71/4.95         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 4.71/4.95      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.71/4.95  thf(t71_enumset1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i]:
% 4.71/4.95     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 4.71/4.95  thf('25', plain,
% 4.71/4.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.71/4.95         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 4.71/4.95      inference('cnf', [status(esa)], [t71_enumset1])).
% 4.71/4.95  thf(t72_enumset1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i,D:$i]:
% 4.71/4.95     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 4.71/4.95  thf('26', plain,
% 4.71/4.95      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.71/4.95         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 4.71/4.95           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 4.71/4.95      inference('cnf', [status(esa)], [t72_enumset1])).
% 4.71/4.95  thf(d3_enumset1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.71/4.95     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 4.71/4.95       ( ![G:$i]:
% 4.71/4.95         ( ( r2_hidden @ G @ F ) <=>
% 4.71/4.95           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 4.71/4.95                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 4.71/4.95  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 4.71/4.95  thf(zf_stmt_7, axiom,
% 4.71/4.95    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 4.71/4.95     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 4.71/4.95       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 4.71/4.95         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 4.71/4.95  thf(zf_stmt_8, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.71/4.95     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 4.71/4.95       ( ![G:$i]:
% 4.71/4.95         ( ( r2_hidden @ G @ F ) <=>
% 4.71/4.95           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 4.71/4.95  thf('27', plain,
% 4.71/4.95      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 4.71/4.95         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 4.71/4.95          | (r2_hidden @ X38 @ X44)
% 4.71/4.95          | ((X44) != (k3_enumset1 @ X43 @ X42 @ X41 @ X40 @ X39)))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_8])).
% 4.71/4.95  thf('28', plain,
% 4.71/4.95      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 4.71/4.95         ((r2_hidden @ X38 @ (k3_enumset1 @ X43 @ X42 @ X41 @ X40 @ X39))
% 4.71/4.95          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 4.71/4.95      inference('simplify', [status(thm)], ['27'])).
% 4.71/4.95  thf('29', plain,
% 4.71/4.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 4.71/4.95         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 4.71/4.95          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 4.71/4.95      inference('sup+', [status(thm)], ['26', '28'])).
% 4.71/4.95  thf('30', plain,
% 4.71/4.95      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.71/4.95         (((X32) != (X31))
% 4.71/4.95          | ~ (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X31))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_7])).
% 4.71/4.95  thf('31', plain,
% 4.71/4.95      (![X31 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 4.71/4.95         ~ (zip_tseitin_0 @ X31 @ X33 @ X34 @ X35 @ X36 @ X31)),
% 4.71/4.95      inference('simplify', [status(thm)], ['30'])).
% 4.71/4.95  thf('32', plain,
% 4.71/4.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.71/4.95         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 4.71/4.95      inference('sup-', [status(thm)], ['29', '31'])).
% 4.71/4.95  thf('33', plain,
% 4.71/4.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.71/4.95         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 4.71/4.95      inference('sup+', [status(thm)], ['25', '32'])).
% 4.71/4.95  thf('34', plain,
% 4.71/4.95      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 4.71/4.95      inference('sup+', [status(thm)], ['24', '33'])).
% 4.71/4.95  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.71/4.95      inference('sup+', [status(thm)], ['23', '34'])).
% 4.71/4.95  thf('36', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 4.71/4.95      inference('sup+', [status(thm)], ['22', '35'])).
% 4.71/4.95  thf(t117_funct_1, axiom,
% 4.71/4.95    (![A:$i,B:$i]:
% 4.71/4.95     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.71/4.95       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 4.71/4.95         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 4.71/4.95  thf('37', plain,
% 4.71/4.95      (![X56 : $i, X57 : $i]:
% 4.71/4.95         (~ (r2_hidden @ X56 @ (k1_relat_1 @ X57))
% 4.71/4.95          | ((k11_relat_1 @ X57 @ X56) = (k1_tarski @ (k1_funct_1 @ X57 @ X56)))
% 4.71/4.95          | ~ (v1_funct_1 @ X57)
% 4.71/4.95          | ~ (v1_relat_1 @ X57))),
% 4.71/4.95      inference('cnf', [status(esa)], [t117_funct_1])).
% 4.71/4.95  thf('38', plain,
% 4.71/4.95      ((~ (v1_relat_1 @ sk_D)
% 4.71/4.95        | ~ (v1_funct_1 @ sk_D)
% 4.71/4.95        | ((k11_relat_1 @ sk_D @ sk_A)
% 4.71/4.95            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 4.71/4.95      inference('sup-', [status(thm)], ['36', '37'])).
% 4.71/4.95  thf('39', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf(cc2_relat_1, axiom,
% 4.71/4.95    (![A:$i]:
% 4.71/4.95     ( ( v1_relat_1 @ A ) =>
% 4.71/4.95       ( ![B:$i]:
% 4.71/4.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.71/4.95  thf('40', plain,
% 4.71/4.95      (![X50 : $i, X51 : $i]:
% 4.71/4.95         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 4.71/4.95          | (v1_relat_1 @ X50)
% 4.71/4.95          | ~ (v1_relat_1 @ X51))),
% 4.71/4.95      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.71/4.95  thf('41', plain,
% 4.71/4.95      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 4.71/4.95        | (v1_relat_1 @ sk_D))),
% 4.71/4.95      inference('sup-', [status(thm)], ['39', '40'])).
% 4.71/4.95  thf(fc6_relat_1, axiom,
% 4.71/4.95    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.71/4.95  thf('42', plain,
% 4.71/4.95      (![X54 : $i, X55 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X54 @ X55))),
% 4.71/4.95      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.71/4.95  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 4.71/4.95      inference('demod', [status(thm)], ['41', '42'])).
% 4.71/4.95  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf('45', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 4.71/4.95      inference('demod', [status(thm)], ['16', '17'])).
% 4.71/4.95  thf(t38_relset_1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.71/4.95       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 4.71/4.95         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.71/4.95  thf('46', plain,
% 4.71/4.95      (![X76 : $i, X77 : $i, X78 : $i]:
% 4.71/4.95         (((k7_relset_1 @ X76 @ X77 @ X78 @ X76)
% 4.71/4.95            = (k2_relset_1 @ X76 @ X77 @ X78))
% 4.71/4.95          | ~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X76 @ X77))))),
% 4.71/4.95      inference('cnf', [status(esa)], [t38_relset_1])).
% 4.71/4.95  thf('47', plain,
% 4.71/4.95      (((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ (k1_relat_1 @ sk_D))
% 4.71/4.95         = (k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D))),
% 4.71/4.95      inference('sup-', [status(thm)], ['45', '46'])).
% 4.71/4.95  thf('48', plain,
% 4.71/4.95      (![X0 : $i]:
% 4.71/4.95         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 4.71/4.95           = (k9_relat_1 @ sk_D @ X0))),
% 4.71/4.95      inference('sup-', [status(thm)], ['18', '19'])).
% 4.71/4.95  thf('49', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 4.71/4.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.71/4.95  thf(redefinition_k2_relset_1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.71/4.95       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.71/4.95  thf('50', plain,
% 4.71/4.95      (![X65 : $i, X66 : $i, X67 : $i]:
% 4.71/4.95         (((k2_relset_1 @ X66 @ X67 @ X65) = (k2_relat_1 @ X65))
% 4.71/4.95          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 4.71/4.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.71/4.95  thf('51', plain,
% 4.71/4.95      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.71/4.95      inference('sup-', [status(thm)], ['49', '50'])).
% 4.71/4.95  thf('52', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 4.71/4.95      inference('demod', [status(thm)], ['3', '10', '13'])).
% 4.71/4.95  thf('53', plain,
% 4.71/4.95      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.71/4.95      inference('demod', [status(thm)], ['51', '52'])).
% 4.71/4.95  thf('54', plain,
% 4.71/4.95      (((k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (k2_relat_1 @ sk_D))),
% 4.71/4.95      inference('demod', [status(thm)], ['47', '48', '53'])).
% 4.71/4.95  thf('55', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 4.71/4.95      inference('demod', [status(thm)], ['3', '10', '13'])).
% 4.71/4.95  thf('56', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 4.71/4.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.71/4.95  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 4.71/4.95      inference('demod', [status(thm)], ['41', '42'])).
% 4.71/4.95  thf('58', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 4.71/4.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.71/4.95  thf(d16_relat_1, axiom,
% 4.71/4.95    (![A:$i]:
% 4.71/4.95     ( ( v1_relat_1 @ A ) =>
% 4.71/4.95       ( ![B:$i]:
% 4.71/4.95         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 4.71/4.95  thf('59', plain,
% 4.71/4.95      (![X52 : $i, X53 : $i]:
% 4.71/4.95         (((k11_relat_1 @ X52 @ X53) = (k9_relat_1 @ X52 @ (k1_tarski @ X53)))
% 4.71/4.95          | ~ (v1_relat_1 @ X52))),
% 4.71/4.95      inference('cnf', [status(esa)], [d16_relat_1])).
% 4.71/4.95  thf('60', plain,
% 4.71/4.95      (![X0 : $i, X1 : $i]:
% 4.71/4.95         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 4.71/4.95          | ~ (v1_relat_1 @ X1))),
% 4.71/4.95      inference('sup+', [status(thm)], ['58', '59'])).
% 4.71/4.95  thf('61', plain,
% 4.71/4.95      (![X0 : $i]:
% 4.71/4.95         ((k11_relat_1 @ sk_D @ X0)
% 4.71/4.95           = (k9_relat_1 @ sk_D @ (k2_tarski @ X0 @ X0)))),
% 4.71/4.95      inference('sup-', [status(thm)], ['57', '60'])).
% 4.71/4.95  thf('62', plain,
% 4.71/4.95      (![X0 : $i]:
% 4.71/4.95         ((k11_relat_1 @ sk_D @ X0) = (k9_relat_1 @ sk_D @ (k1_tarski @ X0)))),
% 4.71/4.95      inference('sup+', [status(thm)], ['56', '61'])).
% 4.71/4.95  thf('63', plain,
% 4.71/4.95      (((k11_relat_1 @ sk_D @ sk_A) = (k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 4.71/4.95      inference('sup+', [status(thm)], ['55', '62'])).
% 4.71/4.95  thf('64', plain, (((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))),
% 4.71/4.95      inference('sup+', [status(thm)], ['54', '63'])).
% 4.71/4.95  thf('65', plain,
% 4.71/4.95      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 4.71/4.95      inference('demod', [status(thm)], ['38', '43', '44', '64'])).
% 4.71/4.95  thf(d10_xboole_0, axiom,
% 4.71/4.95    (![A:$i,B:$i]:
% 4.71/4.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.71/4.95  thf('66', plain,
% 4.71/4.95      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.71/4.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.71/4.95  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.71/4.95      inference('simplify', [status(thm)], ['66'])).
% 4.71/4.95  thf('68', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 4.71/4.95      inference('demod', [status(thm)], ['16', '17'])).
% 4.71/4.95  thf(t14_relset_1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i,D:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 4.71/4.95       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 4.71/4.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 4.71/4.95  thf('69', plain,
% 4.71/4.95      (![X72 : $i, X73 : $i, X74 : $i, X75 : $i]:
% 4.71/4.95         (~ (r1_tarski @ (k2_relat_1 @ X72) @ X73)
% 4.71/4.95          | (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X74 @ X73)))
% 4.71/4.95          | ~ (m1_subset_1 @ X72 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X74 @ X75))))),
% 4.71/4.95      inference('cnf', [status(esa)], [t14_relset_1])).
% 4.71/4.95  thf('70', plain,
% 4.71/4.95      (![X0 : $i]:
% 4.71/4.95         ((m1_subset_1 @ sk_D @ 
% 4.71/4.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 4.71/4.95          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 4.71/4.95      inference('sup-', [status(thm)], ['68', '69'])).
% 4.71/4.95  thf('71', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ 
% 4.71/4.95         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 4.71/4.95      inference('sup-', [status(thm)], ['67', '70'])).
% 4.71/4.95  thf(dt_k7_relset_1, axiom,
% 4.71/4.95    (![A:$i,B:$i,C:$i,D:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.71/4.95       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 4.71/4.95  thf('72', plain,
% 4.71/4.95      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 4.71/4.95         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 4.71/4.95          | (m1_subset_1 @ (k7_relset_1 @ X59 @ X60 @ X58 @ X61) @ 
% 4.71/4.95             (k1_zfmisc_1 @ X60)))),
% 4.71/4.95      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 4.71/4.95  thf('73', plain,
% 4.71/4.95      (![X0 : $i]:
% 4.71/4.95         (m1_subset_1 @ 
% 4.71/4.95          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ sk_D @ X0) @ 
% 4.71/4.95          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D)))),
% 4.71/4.95      inference('sup-', [status(thm)], ['71', '72'])).
% 4.71/4.95  thf('74', plain,
% 4.71/4.95      ((m1_subset_1 @ sk_D @ 
% 4.71/4.95        (k1_zfmisc_1 @ 
% 4.71/4.95         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 4.71/4.95      inference('sup-', [status(thm)], ['67', '70'])).
% 4.71/4.95  thf('75', plain,
% 4.71/4.95      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i]:
% 4.71/4.95         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X70)))
% 4.71/4.95          | ((k7_relset_1 @ X69 @ X70 @ X68 @ X71) = (k9_relat_1 @ X68 @ X71)))),
% 4.71/4.95      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 4.71/4.95  thf('76', plain,
% 4.71/4.95      (![X0 : $i]:
% 4.71/4.95         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ sk_D @ X0)
% 4.71/4.95           = (k9_relat_1 @ sk_D @ X0))),
% 4.71/4.95      inference('sup-', [status(thm)], ['74', '75'])).
% 4.71/4.95  thf('77', plain,
% 4.71/4.95      (![X0 : $i]:
% 4.71/4.95         (m1_subset_1 @ (k9_relat_1 @ sk_D @ X0) @ 
% 4.71/4.95          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D)))),
% 4.71/4.95      inference('demod', [status(thm)], ['73', '76'])).
% 4.71/4.95  thf(t3_subset, axiom,
% 4.71/4.95    (![A:$i,B:$i]:
% 4.71/4.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.71/4.95  thf('78', plain,
% 4.71/4.95      (![X47 : $i, X48 : $i]:
% 4.71/4.95         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 4.71/4.95      inference('cnf', [status(esa)], [t3_subset])).
% 4.71/4.95  thf('79', plain,
% 4.71/4.95      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 4.71/4.95      inference('sup-', [status(thm)], ['77', '78'])).
% 4.71/4.95  thf('80', plain, ($false),
% 4.71/4.95      inference('demod', [status(thm)], ['21', '65', '79'])).
% 4.71/4.95  
% 4.71/4.95  % SZS output end Refutation
% 4.71/4.95  
% 4.71/4.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
