%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b07WFhsGcD

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:04 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 952 expanded)
%              Number of leaves         :   56 ( 316 expanded)
%              Depth                    :   14
%              Number of atoms          : 1023 (10539 expanded)
%              Number of equality atoms :   81 ( 488 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X79: $i,X80: $i,X81: $i,X82: $i] :
      ( ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X80 @ X81 ) ) )
      | ( ( k7_relset_1 @ X80 @ X81 @ X79 @ X82 )
        = ( k9_relat_1 @ X79 @ X82 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X83: $i,X84: $i,X85: $i,X86: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X83 ) @ X84 )
      | ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X85 ) ) )
      | ~ ( m1_subset_1 @ X83 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X86 @ X85 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) @ sk_D )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(d4_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( ( H != F )
              & ( H != E )
              & ( H != D )
              & ( H != C )
              & ( H != B )
              & ( H != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [H: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A )
    <=> ( ( H != A )
        & ( H != B )
        & ( H != C )
        & ( H != D )
        & ( H != E )
        & ( H != F ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( G
        = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) )
    <=> ! [H: $i] :
          ( ( r2_hidden @ H @ G )
        <=> ~ ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      | ( r2_hidden @ X46 @ X53 )
      | ( X53
       != ( k4_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( r2_hidden @ X46 @ ( k4_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 ) )
      | ( zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X5 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( X39 != X38 )
      | ~ ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X38: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ~ ( zip_tseitin_0 @ X38 @ X40 @ X41 @ X42 @ X43 @ X44 @ X38 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X0 @ ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X76: $i,X77: $i,X78: $i] :
      ( ( v4_relat_1 @ X76 @ X77 )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X77 @ X78 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( v4_relat_1 @ X63 @ X64 )
      | ( r1_tarski @ ( k1_relat_1 @ X63 ) @ X64 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X60 ) )
      | ( v1_relat_1 @ X59 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X65: $i,X66: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('41',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
        = ( k1_tarski @ X32 ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X33 @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( r2_hidden @ X74 @ ( k1_relat_1 @ X75 ) )
      | ( ( k11_relat_1 @ X75 @ X74 )
        = ( k1_tarski @ ( k1_funct_1 @ X75 @ X74 ) ) )
      | ~ ( v1_funct_1 @ X75 )
      | ~ ( v1_relat_1 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k11_relat_1 @ sk_D @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ sk_D @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','47'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('49',plain,(
    ! [X61: $i,X62: $i] :
      ( ( ( k11_relat_1 @ X61 @ X62 )
        = ( k9_relat_1 @ X61 @ ( k1_tarski @ X62 ) ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('50',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X72: $i,X73: $i] :
      ( ( X72
        = ( k7_relat_1 @ X72 @ X73 ) )
      | ~ ( v4_relat_1 @ X72 @ X73 )
      | ~ ( v1_relat_1 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('54',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X69: $i,X70: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X69 @ X70 ) )
        = ( k9_relat_1 @ X69 @ X70 ) )
      | ~ ( v1_relat_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k11_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['49','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k11_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','61'])).

thf('63',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('64',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('66',plain,(
    ! [X69: $i,X70: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X69 @ X70 ) )
        = ( k9_relat_1 @ X69 @ X70 ) )
      | ~ ( v1_relat_1 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('67',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X67 @ X68 ) @ ( k2_relat_1 @ X67 ) )
      | ~ ( v1_relat_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) @ X0 ) @ ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('71',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['37','38'])).

thf('72',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','74'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_zfmisc_1 @ X36 @ X37 )
        = k1_xboole_0 )
      | ( X36 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('77',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('78',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','74'])).

thf('80',plain,(
    ! [X37: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('81',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','75','77','78','79','80'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('82',plain,(
    ! [X71: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X71 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('83',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['14','75','77','78','79','80'])).

thf('84',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['4','81','82','83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b07WFhsGcD
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.64  % Solved by: fo/fo7.sh
% 0.44/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.64  % done 423 iterations in 0.182s
% 0.44/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.64  % SZS output start Refutation
% 0.44/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.64  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.44/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.64  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.44/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.44/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.44/0.64  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.44/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $o).
% 0.44/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.64  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.44/0.64  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.44/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.64  thf(t64_funct_2, conjecture,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.64         ( m1_subset_1 @
% 0.44/0.64           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.64       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.64         ( r1_tarski @
% 0.44/0.64           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.44/0.64           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.64            ( m1_subset_1 @
% 0.44/0.64              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.64          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.64            ( r1_tarski @
% 0.44/0.64              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.44/0.64              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.44/0.64    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.44/0.64  thf('0', plain,
% 0.44/0.64      (~ (r1_tarski @ 
% 0.44/0.64          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.44/0.64          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('1', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ 
% 0.44/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(redefinition_k7_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.64       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.44/0.64  thf('2', plain,
% 0.44/0.64      (![X79 : $i, X80 : $i, X81 : $i, X82 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X80 @ X81)))
% 0.44/0.64          | ((k7_relset_1 @ X80 @ X81 @ X79 @ X82) = (k9_relat_1 @ X79 @ X82)))),
% 0.44/0.64      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.44/0.64  thf('3', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.44/0.64           = (k9_relat_1 @ sk_D @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.64  thf('4', plain,
% 0.44/0.64      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.44/0.64          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.64  thf(d10_xboole_0, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.64  thf('5', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.44/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.64  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.44/0.64      inference('simplify', [status(thm)], ['5'])).
% 0.44/0.64  thf('7', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ 
% 0.44/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(t13_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.44/0.64       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.44/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.44/0.64  thf('8', plain,
% 0.44/0.64      (![X83 : $i, X84 : $i, X85 : $i, X86 : $i]:
% 0.44/0.64         (~ (r1_tarski @ (k1_relat_1 @ X83) @ X84)
% 0.44/0.64          | (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X85)))
% 0.44/0.64          | ~ (m1_subset_1 @ X83 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X86 @ X85))))),
% 0.44/0.64      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.44/0.64  thf('9', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.44/0.64          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.64  thf('10', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ 
% 0.44/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['6', '9'])).
% 0.44/0.64  thf(t3_subset, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.64  thf('11', plain,
% 0.44/0.64      (![X56 : $i, X57 : $i]:
% 0.44/0.64         ((r1_tarski @ X56 @ X57) | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X57)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.64  thf('12', plain,
% 0.44/0.64      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.64  thf('13', plain,
% 0.44/0.64      (![X0 : $i, X2 : $i]:
% 0.44/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.64  thf('14', plain,
% 0.44/0.64      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) @ sk_D)
% 0.44/0.64        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B) = (sk_D)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.64  thf(t69_enumset1, axiom,
% 0.44/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.64  thf('15', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.44/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.64  thf(t70_enumset1, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.64  thf('16', plain,
% 0.44/0.64      (![X5 : $i, X6 : $i]:
% 0.44/0.64         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.44/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.64  thf(t71_enumset1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.44/0.64  thf('17', plain,
% 0.44/0.64      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.64         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.44/0.64      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.64  thf(t72_enumset1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.64     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.44/0.64  thf('18', plain,
% 0.44/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.64         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.44/0.64           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.44/0.64      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.44/0.64  thf(t73_enumset1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.44/0.64     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.44/0.64       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.44/0.64  thf('19', plain,
% 0.44/0.64      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.64         ((k4_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.44/0.64           = (k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18))),
% 0.44/0.64      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.44/0.64  thf(d4_enumset1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.44/0.64     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.44/0.64       ( ![H:$i]:
% 0.44/0.64         ( ( r2_hidden @ H @ G ) <=>
% 0.44/0.64           ( ~( ( ( H ) != ( F ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( D ) ) & 
% 0.44/0.64                ( ( H ) != ( C ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( A ) ) ) ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $i > $o).
% 0.44/0.64  thf(zf_stmt_2, axiom,
% 0.44/0.64    (![H:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.44/0.64     ( ( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) <=>
% 0.44/0.64       ( ( ( H ) != ( A ) ) & ( ( H ) != ( B ) ) & ( ( H ) != ( C ) ) & 
% 0.44/0.64         ( ( H ) != ( D ) ) & ( ( H ) != ( E ) ) & ( ( H ) != ( F ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_3, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.44/0.64     ( ( ( G ) = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.44/0.64       ( ![H:$i]:
% 0.44/0.64         ( ( r2_hidden @ H @ G ) <=>
% 0.44/0.64           ( ~( zip_tseitin_0 @ H @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.44/0.64  thf('20', plain,
% 0.44/0.64      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, 
% 0.44/0.64         X53 : $i]:
% 0.44/0.64         ((zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.44/0.64          | (r2_hidden @ X46 @ X53)
% 0.44/0.64          | ((X53) != (k4_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.64  thf('21', plain,
% 0.44/0.64      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.44/0.64         ((r2_hidden @ X46 @ (k4_enumset1 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47))
% 0.44/0.64          | (zip_tseitin_0 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52))),
% 0.44/0.64      inference('simplify', [status(thm)], ['20'])).
% 0.44/0.64  thf('22', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.44/0.64         ((r2_hidden @ X5 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.44/0.64          | (zip_tseitin_0 @ X5 @ X0 @ X1 @ X2 @ X3 @ X4 @ X4))),
% 0.44/0.64      inference('sup+', [status(thm)], ['19', '21'])).
% 0.44/0.64  thf('23', plain,
% 0.44/0.64      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.64         (((X39) != (X38))
% 0.44/0.64          | ~ (zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X38))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.64  thf('24', plain,
% 0.44/0.64      (![X38 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.44/0.64         ~ (zip_tseitin_0 @ X38 @ X40 @ X41 @ X42 @ X43 @ X44 @ X38)),
% 0.44/0.64      inference('simplify', [status(thm)], ['23'])).
% 0.44/0.64  thf('25', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.64         (r2_hidden @ X0 @ (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 0.44/0.64      inference('sup-', [status(thm)], ['22', '24'])).
% 0.44/0.64  thf('26', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.64         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.44/0.64      inference('sup+', [status(thm)], ['18', '25'])).
% 0.44/0.64  thf('27', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.44/0.64      inference('sup+', [status(thm)], ['17', '26'])).
% 0.44/0.64  thf('28', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.44/0.64      inference('sup+', [status(thm)], ['16', '27'])).
% 0.44/0.64  thf('29', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.64      inference('sup+', [status(thm)], ['15', '28'])).
% 0.44/0.64  thf('30', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ 
% 0.44/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(cc2_relset_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.64  thf('31', plain,
% 0.44/0.64      (![X76 : $i, X77 : $i, X78 : $i]:
% 0.44/0.64         ((v4_relat_1 @ X76 @ X77)
% 0.44/0.64          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X77 @ X78))))),
% 0.44/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.64  thf('32', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.64  thf(d18_relat_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ B ) =>
% 0.44/0.64       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.64  thf('33', plain,
% 0.44/0.64      (![X63 : $i, X64 : $i]:
% 0.44/0.64         (~ (v4_relat_1 @ X63 @ X64)
% 0.44/0.64          | (r1_tarski @ (k1_relat_1 @ X63) @ X64)
% 0.44/0.64          | ~ (v1_relat_1 @ X63))),
% 0.44/0.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.44/0.64  thf('34', plain,
% 0.44/0.64      ((~ (v1_relat_1 @ sk_D)
% 0.44/0.64        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.44/0.64  thf('35', plain,
% 0.44/0.64      ((m1_subset_1 @ sk_D @ 
% 0.44/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(cc2_relat_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ A ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.44/0.64  thf('36', plain,
% 0.44/0.64      (![X59 : $i, X60 : $i]:
% 0.44/0.64         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X60))
% 0.44/0.64          | (v1_relat_1 @ X59)
% 0.44/0.64          | ~ (v1_relat_1 @ X60))),
% 0.44/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.64  thf('37', plain,
% 0.44/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.44/0.64        | (v1_relat_1 @ sk_D))),
% 0.44/0.64      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.64  thf(fc6_relat_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.44/0.64  thf('38', plain,
% 0.44/0.64      (![X65 : $i, X66 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X65 @ X66))),
% 0.44/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.44/0.64  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.64      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.64  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.44/0.64      inference('demod', [status(thm)], ['34', '39'])).
% 0.44/0.64  thf(l3_zfmisc_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.44/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.44/0.64  thf('41', plain,
% 0.44/0.64      (![X32 : $i, X33 : $i]:
% 0.44/0.64         (((X33) = (k1_tarski @ X32))
% 0.44/0.64          | ((X33) = (k1_xboole_0))
% 0.44/0.64          | ~ (r1_tarski @ X33 @ (k1_tarski @ X32)))),
% 0.44/0.64      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.44/0.64  thf('42', plain,
% 0.44/0.64      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.44/0.64        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['40', '41'])).
% 0.44/0.64  thf(t117_funct_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.64       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.44/0.64         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.44/0.64  thf('43', plain,
% 0.44/0.64      (![X74 : $i, X75 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X74 @ (k1_relat_1 @ X75))
% 0.44/0.64          | ((k11_relat_1 @ X75 @ X74) = (k1_tarski @ (k1_funct_1 @ X75 @ X74)))
% 0.44/0.64          | ~ (v1_funct_1 @ X75)
% 0.44/0.64          | ~ (v1_relat_1 @ X75))),
% 0.44/0.64      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.44/0.64  thf('44', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.44/0.64          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.44/0.64          | ~ (v1_relat_1 @ sk_D)
% 0.44/0.64          | ~ (v1_funct_1 @ sk_D)
% 0.44/0.64          | ((k11_relat_1 @ sk_D @ X0) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['42', '43'])).
% 0.44/0.64  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.64      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.64  thf('46', plain, ((v1_funct_1 @ sk_D)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('47', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.44/0.64          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.44/0.64          | ((k11_relat_1 @ sk_D @ X0) = (k1_tarski @ (k1_funct_1 @ sk_D @ X0))))),
% 0.44/0.64      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.44/0.64  thf('48', plain,
% 0.44/0.64      ((((k11_relat_1 @ sk_D @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.44/0.64        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['29', '47'])).
% 0.44/0.64  thf(d16_relat_1, axiom,
% 0.44/0.64    (![A:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ A ) =>
% 0.44/0.64       ( ![B:$i]:
% 0.44/0.64         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.44/0.64  thf('49', plain,
% 0.44/0.64      (![X61 : $i, X62 : $i]:
% 0.44/0.64         (((k11_relat_1 @ X61 @ X62) = (k9_relat_1 @ X61 @ (k1_tarski @ X62)))
% 0.44/0.64          | ~ (v1_relat_1 @ X61))),
% 0.44/0.64      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.44/0.64  thf('50', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['30', '31'])).
% 0.44/0.64  thf(t209_relat_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.44/0.64       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.44/0.64  thf('51', plain,
% 0.44/0.64      (![X72 : $i, X73 : $i]:
% 0.44/0.64         (((X72) = (k7_relat_1 @ X72 @ X73))
% 0.44/0.64          | ~ (v4_relat_1 @ X72 @ X73)
% 0.44/0.64          | ~ (v1_relat_1 @ X72))),
% 0.44/0.64      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.44/0.64  thf('52', plain,
% 0.44/0.64      ((~ (v1_relat_1 @ sk_D)
% 0.44/0.64        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['50', '51'])).
% 0.44/0.64  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.64      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.64  thf('54', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.44/0.64  thf(t148_relat_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ B ) =>
% 0.44/0.64       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.44/0.64  thf('55', plain,
% 0.44/0.64      (![X69 : $i, X70 : $i]:
% 0.44/0.64         (((k2_relat_1 @ (k7_relat_1 @ X69 @ X70)) = (k9_relat_1 @ X69 @ X70))
% 0.44/0.64          | ~ (v1_relat_1 @ X69))),
% 0.44/0.64      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.44/0.64  thf('56', plain,
% 0.44/0.64      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 0.44/0.64        | ~ (v1_relat_1 @ sk_D))),
% 0.44/0.64      inference('sup+', [status(thm)], ['54', '55'])).
% 0.44/0.64  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.64      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.64  thf('58', plain,
% 0.44/0.64      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.44/0.64  thf('59', plain,
% 0.44/0.64      ((((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))
% 0.44/0.64        | ~ (v1_relat_1 @ sk_D))),
% 0.44/0.64      inference('sup+', [status(thm)], ['49', '58'])).
% 0.44/0.64  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.64      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.64  thf('61', plain, (((k2_relat_1 @ sk_D) = (k11_relat_1 @ sk_D @ sk_A))),
% 0.44/0.64      inference('demod', [status(thm)], ['59', '60'])).
% 0.44/0.64  thf('62', plain,
% 0.44/0.64      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.44/0.64        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.44/0.64      inference('demod', [status(thm)], ['48', '61'])).
% 0.44/0.64  thf('63', plain,
% 0.44/0.64      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.44/0.64          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.64  thf('64', plain,
% 0.44/0.64      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.44/0.64        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.44/0.64  thf('65', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.44/0.64  thf('66', plain,
% 0.44/0.64      (![X69 : $i, X70 : $i]:
% 0.44/0.64         (((k2_relat_1 @ (k7_relat_1 @ X69 @ X70)) = (k9_relat_1 @ X69 @ X70))
% 0.44/0.64          | ~ (v1_relat_1 @ X69))),
% 0.44/0.64      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.44/0.64  thf(t144_relat_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( v1_relat_1 @ B ) =>
% 0.44/0.64       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.44/0.64  thf('67', plain,
% 0.44/0.64      (![X67 : $i, X68 : $i]:
% 0.44/0.64         ((r1_tarski @ (k9_relat_1 @ X67 @ X68) @ (k2_relat_1 @ X67))
% 0.44/0.64          | ~ (v1_relat_1 @ X67))),
% 0.44/0.64      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.44/0.64  thf('68', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.64         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.44/0.64           (k9_relat_1 @ X1 @ X0))
% 0.44/0.64          | ~ (v1_relat_1 @ X1)
% 0.44/0.64          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.44/0.64      inference('sup+', [status(thm)], ['66', '67'])).
% 0.44/0.64  thf('69', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         (~ (v1_relat_1 @ sk_D)
% 0.44/0.64          | ~ (v1_relat_1 @ sk_D)
% 0.44/0.64          | (r1_tarski @ 
% 0.44/0.64             (k9_relat_1 @ (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)) @ X0) @ 
% 0.44/0.64             (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.44/0.64      inference('sup-', [status(thm)], ['65', '68'])).
% 0.44/0.64  thf('70', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.64      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.64  thf('71', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.64      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.64  thf('72', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['52', '53'])).
% 0.44/0.64  thf('73', plain,
% 0.44/0.64      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.44/0.64      inference('demod', [status(thm)], ['56', '57'])).
% 0.44/0.64  thf('74', plain,
% 0.44/0.64      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.44/0.64      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.44/0.64  thf('75', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.64      inference('demod', [status(thm)], ['64', '74'])).
% 0.44/0.64  thf(t113_zfmisc_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.44/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.44/0.64  thf('76', plain,
% 0.44/0.64      (![X36 : $i, X37 : $i]:
% 0.44/0.64         (((k2_zfmisc_1 @ X36 @ X37) = (k1_xboole_0))
% 0.44/0.64          | ((X36) != (k1_xboole_0)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.44/0.64  thf('77', plain,
% 0.44/0.64      (![X37 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.44/0.64      inference('simplify', [status(thm)], ['76'])).
% 0.44/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.44/0.64  thf('78', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.44/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.64  thf('79', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.44/0.64      inference('demod', [status(thm)], ['64', '74'])).
% 0.44/0.64  thf('80', plain,
% 0.44/0.64      (![X37 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.44/0.64      inference('simplify', [status(thm)], ['76'])).
% 0.44/0.64  thf('81', plain, (((k1_xboole_0) = (sk_D))),
% 0.44/0.64      inference('demod', [status(thm)], ['14', '75', '77', '78', '79', '80'])).
% 0.44/0.64  thf(t150_relat_1, axiom,
% 0.44/0.64    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.44/0.64  thf('82', plain,
% 0.44/0.64      (![X71 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X71) = (k1_xboole_0))),
% 0.44/0.64      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.44/0.64  thf('83', plain, (((k1_xboole_0) = (sk_D))),
% 0.44/0.64      inference('demod', [status(thm)], ['14', '75', '77', '78', '79', '80'])).
% 0.44/0.64  thf('84', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.44/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.44/0.64  thf('85', plain, ($false),
% 0.44/0.64      inference('demod', [status(thm)], ['4', '81', '82', '83', '84'])).
% 0.44/0.64  
% 0.44/0.64  % SZS output end Refutation
% 0.44/0.64  
% 0.44/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
