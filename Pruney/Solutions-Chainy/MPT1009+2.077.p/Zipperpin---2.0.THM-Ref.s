%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.glHGqkdDhJ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:59 EST 2020

% Result     : Theorem 6.42s
% Output     : Refutation 6.42s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 335 expanded)
%              Number of leaves         :   56 ( 124 expanded)
%              Depth                    :   15
%              Number of atoms          : 1061 (4333 expanded)
%              Number of equality atoms :   75 ( 242 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X71 ) @ X72 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X71 ) @ X73 )
      | ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X73 ) ) )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ( ( k7_relset_1 @ X68 @ X69 @ X67 @ X70 )
        = ( k9_relat_1 @ X67 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X59 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X58 @ X59 @ X57 @ X60 ) @ ( k1_zfmisc_1 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_tarski @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ~ ( v1_funct_2 @ X81 @ X79 @ X80 )
      | ( X79
        = ( k1_relset_1 @ X79 @ X80 @ X81 ) )
      | ~ ( zip_tseitin_2 @ X81 @ X80 @ X79 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ~ ( zip_tseitin_2 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('19',plain,(
    ! [X77: $i,X78: $i] :
      ( ( zip_tseitin_1 @ X77 @ X78 )
      | ( X77 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X82: $i,X83: $i,X84: $i] :
      ( ~ ( zip_tseitin_1 @ X82 @ X83 )
      | ( zip_tseitin_2 @ X84 @ X82 @ X83 )
      | ~ ( m1_subset_1 @ X84 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X83 @ X82 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( zip_tseitin_2 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    zip_tseitin_2 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( ( k1_relset_1 @ X62 @ X63 @ X61 )
        = ( k1_relat_1 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ( ( k7_relset_1 @ X68 @ X69 @ X67 @ X70 )
        = ( k9_relat_1 @ X67 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X6 @ X6 @ X7 @ X8 )
      = ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('41',plain,(
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

thf('42',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      | ( r2_hidden @ X38 @ X44 )
      | ( X44
       != ( k3_enumset1 @ X43 @ X42 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('43',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ X38 @ ( k3_enumset1 @ X43 @ X42 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X32 != X31 )
      | ~ ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('46',plain,(
    ! [X31: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X31 @ X33 @ X34 @ X35 @ X36 @ X31 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','49'])).

thf('51',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['37','50'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ ( k1_relat_1 @ X53 ) )
      | ( ( k11_relat_1 @ X53 @ X52 )
        = ( k1_tarski @ ( k1_funct_1 @ X53 @ X52 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('55',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( v1_relat_1 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('59',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k11_relat_1 @ X50 @ X51 )
        = ( k9_relat_1 @ X50 @ ( k1_tarski @ X51 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('62',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ( ( k7_relset_1 @ X74 @ X75 @ X76 @ X74 )
        = ( k2_relset_1 @ X74 @ X75 @ X76 ) )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X74 @ X75 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('63',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('66',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( ( k2_relset_1 @ X65 @ X66 @ X64 )
        = ( k2_relat_1 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X66 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('67',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['18','25','28'])).

thf('69',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','69'])).

thf('71',plain,
    ( ( ( k11_relat_1 @ sk_D @ sk_A )
      = ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['60','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('73',plain,
    ( ( k11_relat_1 @ sk_D @ sk_A )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','56','57','73'])).

thf('75',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['36','74'])).

thf('76',plain,(
    ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['54','55'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.glHGqkdDhJ
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:24:02 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 6.42/6.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.42/6.62  % Solved by: fo/fo7.sh
% 6.42/6.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.42/6.62  % done 2168 iterations in 6.133s
% 6.42/6.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.42/6.62  % SZS output start Refutation
% 6.42/6.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.42/6.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.42/6.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 6.42/6.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.42/6.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.42/6.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.42/6.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.42/6.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.42/6.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.42/6.62  thf(sk_A_type, type, sk_A: $i).
% 6.42/6.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.42/6.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 6.42/6.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.42/6.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.42/6.62  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 6.42/6.62  thf(sk_D_type, type, sk_D: $i).
% 6.42/6.62  thf(sk_C_type, type, sk_C: $i).
% 6.42/6.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.42/6.62  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 6.42/6.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.42/6.62  thf(sk_B_type, type, sk_B: $i).
% 6.42/6.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.42/6.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.42/6.62  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 6.42/6.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.42/6.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.42/6.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.42/6.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.42/6.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 6.42/6.62  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 6.42/6.62  thf(d10_xboole_0, axiom,
% 6.42/6.62    (![A:$i,B:$i]:
% 6.42/6.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.42/6.62  thf('0', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.42/6.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.42/6.62  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.42/6.62      inference('simplify', [status(thm)], ['0'])).
% 6.42/6.62  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.42/6.62      inference('simplify', [status(thm)], ['0'])).
% 6.42/6.62  thf(t11_relset_1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i]:
% 6.42/6.62     ( ( v1_relat_1 @ C ) =>
% 6.42/6.62       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 6.42/6.62           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 6.42/6.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 6.42/6.62  thf('3', plain,
% 6.42/6.62      (![X71 : $i, X72 : $i, X73 : $i]:
% 6.42/6.62         (~ (r1_tarski @ (k1_relat_1 @ X71) @ X72)
% 6.42/6.62          | ~ (r1_tarski @ (k2_relat_1 @ X71) @ X73)
% 6.42/6.62          | (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X73)))
% 6.42/6.62          | ~ (v1_relat_1 @ X71))),
% 6.42/6.62      inference('cnf', [status(esa)], [t11_relset_1])).
% 6.42/6.62  thf('4', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i]:
% 6.42/6.62         (~ (v1_relat_1 @ X0)
% 6.42/6.62          | (m1_subset_1 @ X0 @ 
% 6.42/6.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 6.42/6.62          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 6.42/6.62      inference('sup-', [status(thm)], ['2', '3'])).
% 6.42/6.62  thf('5', plain,
% 6.42/6.62      (![X0 : $i]:
% 6.42/6.62         ((m1_subset_1 @ X0 @ 
% 6.42/6.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 6.42/6.62          | ~ (v1_relat_1 @ X0))),
% 6.42/6.62      inference('sup-', [status(thm)], ['1', '4'])).
% 6.42/6.62  thf(redefinition_k7_relset_1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.42/6.62       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 6.42/6.62  thf('6', plain,
% 6.42/6.62      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 6.42/6.62         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 6.42/6.62          | ((k7_relset_1 @ X68 @ X69 @ X67 @ X70) = (k9_relat_1 @ X67 @ X70)))),
% 6.42/6.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 6.42/6.62  thf('7', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i]:
% 6.42/6.62         (~ (v1_relat_1 @ X0)
% 6.42/6.62          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 6.42/6.62              = (k9_relat_1 @ X0 @ X1)))),
% 6.42/6.62      inference('sup-', [status(thm)], ['5', '6'])).
% 6.42/6.62  thf('8', plain,
% 6.42/6.62      (![X0 : $i]:
% 6.42/6.62         ((m1_subset_1 @ X0 @ 
% 6.42/6.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 6.42/6.62          | ~ (v1_relat_1 @ X0))),
% 6.42/6.62      inference('sup-', [status(thm)], ['1', '4'])).
% 6.42/6.62  thf(dt_k7_relset_1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.42/6.62       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 6.42/6.62  thf('9', plain,
% 6.42/6.62      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 6.42/6.62         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X59)))
% 6.42/6.62          | (m1_subset_1 @ (k7_relset_1 @ X58 @ X59 @ X57 @ X60) @ 
% 6.42/6.62             (k1_zfmisc_1 @ X59)))),
% 6.42/6.62      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 6.42/6.62  thf('10', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i]:
% 6.42/6.62         (~ (v1_relat_1 @ X0)
% 6.42/6.62          | (m1_subset_1 @ 
% 6.42/6.62             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 6.42/6.62             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 6.42/6.62      inference('sup-', [status(thm)], ['8', '9'])).
% 6.42/6.62  thf('11', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i]:
% 6.42/6.62         ((m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 6.42/6.62           (k1_zfmisc_1 @ (k2_relat_1 @ X1)))
% 6.42/6.62          | ~ (v1_relat_1 @ X1)
% 6.42/6.62          | ~ (v1_relat_1 @ X1))),
% 6.42/6.62      inference('sup+', [status(thm)], ['7', '10'])).
% 6.42/6.62  thf('12', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i]:
% 6.42/6.62         (~ (v1_relat_1 @ X1)
% 6.42/6.62          | (m1_subset_1 @ (k9_relat_1 @ X1 @ X0) @ 
% 6.42/6.62             (k1_zfmisc_1 @ (k2_relat_1 @ X1))))),
% 6.42/6.62      inference('simplify', [status(thm)], ['11'])).
% 6.42/6.62  thf(t3_subset, axiom,
% 6.42/6.62    (![A:$i,B:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.42/6.62  thf('13', plain,
% 6.42/6.62      (![X47 : $i, X48 : $i]:
% 6.42/6.62         ((r1_tarski @ X47 @ X48) | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48)))),
% 6.42/6.62      inference('cnf', [status(esa)], [t3_subset])).
% 6.42/6.62  thf('14', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i]:
% 6.42/6.62         (~ (v1_relat_1 @ X0)
% 6.42/6.62          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ (k2_relat_1 @ X0)))),
% 6.42/6.62      inference('sup-', [status(thm)], ['12', '13'])).
% 6.42/6.62  thf(t64_funct_2, conjecture,
% 6.42/6.62    (![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 6.42/6.62         ( m1_subset_1 @
% 6.42/6.62           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 6.42/6.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 6.42/6.62         ( r1_tarski @
% 6.42/6.62           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 6.42/6.62           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 6.42/6.62  thf(zf_stmt_0, negated_conjecture,
% 6.42/6.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 6.42/6.62            ( m1_subset_1 @
% 6.42/6.62              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 6.42/6.62          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 6.42/6.62            ( r1_tarski @
% 6.42/6.62              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 6.42/6.62              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 6.42/6.62    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 6.42/6.62  thf('15', plain,
% 6.42/6.62      (~ (r1_tarski @ 
% 6.42/6.62          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 6.42/6.62          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf('16', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf(d1_funct_2, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.42/6.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.42/6.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.42/6.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.42/6.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.42/6.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.42/6.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.42/6.62  thf(zf_stmt_1, axiom,
% 6.42/6.62    (![C:$i,B:$i,A:$i]:
% 6.42/6.62     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 6.42/6.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.42/6.62  thf('17', plain,
% 6.42/6.62      (![X79 : $i, X80 : $i, X81 : $i]:
% 6.42/6.62         (~ (v1_funct_2 @ X81 @ X79 @ X80)
% 6.42/6.62          | ((X79) = (k1_relset_1 @ X79 @ X80 @ X81))
% 6.42/6.62          | ~ (zip_tseitin_2 @ X81 @ X80 @ X79))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.42/6.62  thf('18', plain,
% 6.42/6.62      ((~ (zip_tseitin_2 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 6.42/6.62        | ((k1_tarski @ sk_A)
% 6.42/6.62            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 6.42/6.62      inference('sup-', [status(thm)], ['16', '17'])).
% 6.42/6.62  thf(zf_stmt_2, axiom,
% 6.42/6.62    (![B:$i,A:$i]:
% 6.42/6.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.42/6.62       ( zip_tseitin_1 @ B @ A ) ))).
% 6.42/6.62  thf('19', plain,
% 6.42/6.62      (![X77 : $i, X78 : $i]:
% 6.42/6.62         ((zip_tseitin_1 @ X77 @ X78) | ((X77) = (k1_xboole_0)))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 6.42/6.62  thf('20', plain,
% 6.42/6.62      ((m1_subset_1 @ sk_D @ 
% 6.42/6.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 6.42/6.62  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 6.42/6.62  thf(zf_stmt_5, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.42/6.62       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 6.42/6.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.42/6.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.42/6.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.42/6.62  thf('21', plain,
% 6.42/6.62      (![X82 : $i, X83 : $i, X84 : $i]:
% 6.42/6.62         (~ (zip_tseitin_1 @ X82 @ X83)
% 6.42/6.62          | (zip_tseitin_2 @ X84 @ X82 @ X83)
% 6.42/6.62          | ~ (m1_subset_1 @ X84 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X83 @ X82))))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.42/6.62  thf('22', plain,
% 6.42/6.62      (((zip_tseitin_2 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 6.42/6.62        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 6.42/6.62      inference('sup-', [status(thm)], ['20', '21'])).
% 6.42/6.62  thf('23', plain,
% 6.42/6.62      ((((sk_B) = (k1_xboole_0))
% 6.42/6.62        | (zip_tseitin_2 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 6.42/6.62      inference('sup-', [status(thm)], ['19', '22'])).
% 6.42/6.62  thf('24', plain, (((sk_B) != (k1_xboole_0))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf('25', plain, ((zip_tseitin_2 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 6.42/6.62      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 6.42/6.62  thf('26', plain,
% 6.42/6.62      ((m1_subset_1 @ sk_D @ 
% 6.42/6.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf(redefinition_k1_relset_1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.42/6.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.42/6.62  thf('27', plain,
% 6.42/6.62      (![X61 : $i, X62 : $i, X63 : $i]:
% 6.42/6.62         (((k1_relset_1 @ X62 @ X63 @ X61) = (k1_relat_1 @ X61))
% 6.42/6.62          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 6.42/6.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.42/6.62  thf('28', plain,
% 6.42/6.62      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.42/6.62      inference('sup-', [status(thm)], ['26', '27'])).
% 6.42/6.62  thf('29', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['18', '25', '28'])).
% 6.42/6.62  thf('30', plain,
% 6.42/6.62      (~ (r1_tarski @ 
% 6.42/6.62          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 6.42/6.62          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 6.42/6.62      inference('demod', [status(thm)], ['15', '29'])).
% 6.42/6.62  thf('31', plain,
% 6.42/6.62      ((m1_subset_1 @ sk_D @ 
% 6.42/6.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf('32', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['18', '25', '28'])).
% 6.42/6.62  thf('33', plain,
% 6.42/6.62      ((m1_subset_1 @ sk_D @ 
% 6.42/6.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 6.42/6.62      inference('demod', [status(thm)], ['31', '32'])).
% 6.42/6.62  thf('34', plain,
% 6.42/6.62      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 6.42/6.62         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 6.42/6.62          | ((k7_relset_1 @ X68 @ X69 @ X67 @ X70) = (k9_relat_1 @ X67 @ X70)))),
% 6.42/6.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 6.42/6.62  thf('35', plain,
% 6.42/6.62      (![X0 : $i]:
% 6.42/6.62         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 6.42/6.62           = (k9_relat_1 @ sk_D @ X0))),
% 6.42/6.62      inference('sup-', [status(thm)], ['33', '34'])).
% 6.42/6.62  thf('36', plain,
% 6.42/6.62      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 6.42/6.62          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 6.42/6.62      inference('demod', [status(thm)], ['30', '35'])).
% 6.42/6.62  thf('37', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['18', '25', '28'])).
% 6.42/6.62  thf(t69_enumset1, axiom,
% 6.42/6.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.42/6.62  thf('38', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 6.42/6.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.42/6.62  thf(t70_enumset1, axiom,
% 6.42/6.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 6.42/6.62  thf('39', plain,
% 6.42/6.62      (![X4 : $i, X5 : $i]:
% 6.42/6.62         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 6.42/6.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.42/6.62  thf(t71_enumset1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i]:
% 6.42/6.62     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 6.42/6.62  thf('40', plain,
% 6.42/6.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 6.42/6.62         ((k2_enumset1 @ X6 @ X6 @ X7 @ X8) = (k1_enumset1 @ X6 @ X7 @ X8))),
% 6.42/6.62      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.42/6.62  thf(t72_enumset1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i,D:$i]:
% 6.42/6.62     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 6.42/6.62  thf('41', plain,
% 6.42/6.62      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 6.42/6.62         ((k3_enumset1 @ X9 @ X9 @ X10 @ X11 @ X12)
% 6.42/6.62           = (k2_enumset1 @ X9 @ X10 @ X11 @ X12))),
% 6.42/6.62      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.42/6.62  thf(d3_enumset1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.42/6.62     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 6.42/6.62       ( ![G:$i]:
% 6.42/6.62         ( ( r2_hidden @ G @ F ) <=>
% 6.42/6.62           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 6.42/6.62                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 6.42/6.62  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 6.42/6.62  thf(zf_stmt_7, axiom,
% 6.42/6.62    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 6.42/6.62     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 6.42/6.62       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 6.42/6.62         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 6.42/6.62  thf(zf_stmt_8, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.42/6.62     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 6.42/6.62       ( ![G:$i]:
% 6.42/6.62         ( ( r2_hidden @ G @ F ) <=>
% 6.42/6.62           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 6.42/6.62  thf('42', plain,
% 6.42/6.62      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 6.42/6.62         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 6.42/6.62          | (r2_hidden @ X38 @ X44)
% 6.42/6.62          | ((X44) != (k3_enumset1 @ X43 @ X42 @ X41 @ X40 @ X39)))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_8])).
% 6.42/6.62  thf('43', plain,
% 6.42/6.62      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 6.42/6.62         ((r2_hidden @ X38 @ (k3_enumset1 @ X43 @ X42 @ X41 @ X40 @ X39))
% 6.42/6.62          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 6.42/6.62      inference('simplify', [status(thm)], ['42'])).
% 6.42/6.62  thf('44', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.42/6.62         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 6.42/6.62          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 6.42/6.62      inference('sup+', [status(thm)], ['41', '43'])).
% 6.42/6.62  thf('45', plain,
% 6.42/6.62      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 6.42/6.62         (((X32) != (X31))
% 6.42/6.62          | ~ (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X31))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_7])).
% 6.42/6.62  thf('46', plain,
% 6.42/6.62      (![X31 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 6.42/6.62         ~ (zip_tseitin_0 @ X31 @ X33 @ X34 @ X35 @ X36 @ X31)),
% 6.42/6.62      inference('simplify', [status(thm)], ['45'])).
% 6.42/6.62  thf('47', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.42/6.62         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 6.42/6.62      inference('sup-', [status(thm)], ['44', '46'])).
% 6.42/6.62  thf('48', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.42/6.62         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 6.42/6.62      inference('sup+', [status(thm)], ['40', '47'])).
% 6.42/6.62  thf('49', plain,
% 6.42/6.62      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 6.42/6.62      inference('sup+', [status(thm)], ['39', '48'])).
% 6.42/6.62  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 6.42/6.62      inference('sup+', [status(thm)], ['38', '49'])).
% 6.42/6.62  thf('51', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 6.42/6.62      inference('sup+', [status(thm)], ['37', '50'])).
% 6.42/6.62  thf(t117_funct_1, axiom,
% 6.42/6.62    (![A:$i,B:$i]:
% 6.42/6.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.42/6.62       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 6.42/6.62         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 6.42/6.62  thf('52', plain,
% 6.42/6.62      (![X52 : $i, X53 : $i]:
% 6.42/6.62         (~ (r2_hidden @ X52 @ (k1_relat_1 @ X53))
% 6.42/6.62          | ((k11_relat_1 @ X53 @ X52) = (k1_tarski @ (k1_funct_1 @ X53 @ X52)))
% 6.42/6.62          | ~ (v1_funct_1 @ X53)
% 6.42/6.62          | ~ (v1_relat_1 @ X53))),
% 6.42/6.62      inference('cnf', [status(esa)], [t117_funct_1])).
% 6.42/6.62  thf('53', plain,
% 6.42/6.62      ((~ (v1_relat_1 @ sk_D)
% 6.42/6.62        | ~ (v1_funct_1 @ sk_D)
% 6.42/6.62        | ((k11_relat_1 @ sk_D @ sk_A)
% 6.42/6.62            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 6.42/6.62      inference('sup-', [status(thm)], ['51', '52'])).
% 6.42/6.62  thf('54', plain,
% 6.42/6.62      ((m1_subset_1 @ sk_D @ 
% 6.42/6.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf(cc1_relset_1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.42/6.62       ( v1_relat_1 @ C ) ))).
% 6.42/6.62  thf('55', plain,
% 6.42/6.62      (![X54 : $i, X55 : $i, X56 : $i]:
% 6.42/6.62         ((v1_relat_1 @ X54)
% 6.42/6.62          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56))))),
% 6.42/6.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.42/6.62  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 6.42/6.62      inference('sup-', [status(thm)], ['54', '55'])).
% 6.42/6.62  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf('58', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['18', '25', '28'])).
% 6.42/6.62  thf(d16_relat_1, axiom,
% 6.42/6.62    (![A:$i]:
% 6.42/6.62     ( ( v1_relat_1 @ A ) =>
% 6.42/6.62       ( ![B:$i]:
% 6.42/6.62         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 6.42/6.62  thf('59', plain,
% 6.42/6.62      (![X50 : $i, X51 : $i]:
% 6.42/6.62         (((k11_relat_1 @ X50 @ X51) = (k9_relat_1 @ X50 @ (k1_tarski @ X51)))
% 6.42/6.62          | ~ (v1_relat_1 @ X50))),
% 6.42/6.62      inference('cnf', [status(esa)], [d16_relat_1])).
% 6.42/6.62  thf('60', plain,
% 6.42/6.62      (![X0 : $i]:
% 6.42/6.62         (((k11_relat_1 @ X0 @ sk_A) = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D)))
% 6.42/6.62          | ~ (v1_relat_1 @ X0))),
% 6.42/6.62      inference('sup+', [status(thm)], ['58', '59'])).
% 6.42/6.62  thf('61', plain,
% 6.42/6.62      ((m1_subset_1 @ sk_D @ 
% 6.42/6.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 6.42/6.62      inference('demod', [status(thm)], ['31', '32'])).
% 6.42/6.62  thf(t38_relset_1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.42/6.62       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 6.42/6.62         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.42/6.62  thf('62', plain,
% 6.42/6.62      (![X74 : $i, X75 : $i, X76 : $i]:
% 6.42/6.62         (((k7_relset_1 @ X74 @ X75 @ X76 @ X74)
% 6.42/6.62            = (k2_relset_1 @ X74 @ X75 @ X76))
% 6.42/6.62          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X74 @ X75))))),
% 6.42/6.62      inference('cnf', [status(esa)], [t38_relset_1])).
% 6.42/6.62  thf('63', plain,
% 6.42/6.62      (((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ (k1_relat_1 @ sk_D))
% 6.42/6.62         = (k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D))),
% 6.42/6.62      inference('sup-', [status(thm)], ['61', '62'])).
% 6.42/6.62  thf('64', plain,
% 6.42/6.62      (![X0 : $i]:
% 6.42/6.62         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 6.42/6.62           = (k9_relat_1 @ sk_D @ X0))),
% 6.42/6.62      inference('sup-', [status(thm)], ['33', '34'])).
% 6.42/6.62  thf('65', plain,
% 6.42/6.62      ((m1_subset_1 @ sk_D @ 
% 6.42/6.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 6.42/6.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.42/6.62  thf(redefinition_k2_relset_1, axiom,
% 6.42/6.62    (![A:$i,B:$i,C:$i]:
% 6.42/6.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.42/6.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.42/6.62  thf('66', plain,
% 6.42/6.62      (![X64 : $i, X65 : $i, X66 : $i]:
% 6.42/6.62         (((k2_relset_1 @ X65 @ X66 @ X64) = (k2_relat_1 @ X64))
% 6.42/6.62          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X66))))),
% 6.42/6.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.42/6.62  thf('67', plain,
% 6.42/6.62      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 6.42/6.62      inference('sup-', [status(thm)], ['65', '66'])).
% 6.42/6.62  thf('68', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['18', '25', '28'])).
% 6.42/6.62  thf('69', plain,
% 6.42/6.62      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['67', '68'])).
% 6.42/6.62  thf('70', plain,
% 6.42/6.62      (((k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (k2_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['63', '64', '69'])).
% 6.42/6.62  thf('71', plain,
% 6.42/6.62      ((((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))
% 6.42/6.62        | ~ (v1_relat_1 @ sk_D))),
% 6.42/6.62      inference('sup+', [status(thm)], ['60', '70'])).
% 6.42/6.62  thf('72', plain, ((v1_relat_1 @ sk_D)),
% 6.42/6.62      inference('sup-', [status(thm)], ['54', '55'])).
% 6.42/6.62  thf('73', plain, (((k11_relat_1 @ sk_D @ sk_A) = (k2_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['71', '72'])).
% 6.42/6.62  thf('74', plain,
% 6.42/6.62      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 6.42/6.62      inference('demod', [status(thm)], ['53', '56', '57', '73'])).
% 6.42/6.62  thf('75', plain,
% 6.42/6.62      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 6.42/6.62      inference('demod', [status(thm)], ['36', '74'])).
% 6.42/6.62  thf('76', plain, (~ (v1_relat_1 @ sk_D)),
% 6.42/6.62      inference('sup-', [status(thm)], ['14', '75'])).
% 6.42/6.62  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 6.42/6.62      inference('sup-', [status(thm)], ['54', '55'])).
% 6.42/6.62  thf('78', plain, ($false), inference('demod', [status(thm)], ['76', '77'])).
% 6.42/6.62  
% 6.42/6.62  % SZS output end Refutation
% 6.42/6.62  
% 6.42/6.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
