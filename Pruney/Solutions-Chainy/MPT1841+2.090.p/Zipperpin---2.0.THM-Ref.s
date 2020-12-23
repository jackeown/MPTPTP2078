%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uUm6Yn0LCB

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:41 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 109 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  642 ( 869 expanded)
%              Number of equality atoms :   42 (  45 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X62: $i,X63: $i] :
      ( ( v1_xboole_0 @ X62 )
      | ~ ( m1_subset_1 @ X63 @ X62 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X64: $i,X65: $i] :
      ( ( v1_xboole_0 @ X64 )
      | ~ ( m1_subset_1 @ X65 @ X64 )
      | ( ( k6_domain_1 @ X64 @ X65 )
        = ( k1_tarski @ X65 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ X67 ) )
      | ~ ( v1_subset_1 @ X66 @ X67 )
      | ( v1_xboole_0 @ X66 )
      | ~ ( v1_zfmisc_1 @ X67 )
      | ( v1_xboole_0 @ X67 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k5_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k6_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(d6_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( ( J != H )
              & ( J != G )
              & ( J != F )
              & ( J != E )
              & ( J != D )
              & ( J != C )
              & ( J != B )
              & ( J != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [J: $i,H: $i,G: $i,F: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A )
    <=> ( ( J != A )
        & ( J != B )
        & ( J != C )
        & ( J != D )
        & ( J != E )
        & ( J != F )
        & ( J != G )
        & ( J != H ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( I
        = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) )
    <=> ! [J: $i] :
          ( ( r2_hidden @ J @ I )
        <=> ~ ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      | ( r2_hidden @ X39 @ X48 )
      | ( X48
       != ( k6_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( r2_hidden @ X39 @ ( k6_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40 ) )
      | ( zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( X30 != X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X29: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ~ ( zip_tseitin_0 @ X29 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X29 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( r2_hidden @ X60 @ X61 )
      | ~ ( r1_tarski @ X61 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ~ ( r1_tarski @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( r1_tarski @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( r1_tarski @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X4 ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X3 ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r1_tarski @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X2 ) ),
    inference('sup-',[status(thm)],['24','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['23','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','42'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X51: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uUm6Yn0LCB
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.54  % Solved by: fo/fo7.sh
% 0.38/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.54  % done 134 iterations in 0.086s
% 0.38/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.54  % SZS output start Refutation
% 0.38/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.54  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.38/0.54                                               $i > $i > $i > $o).
% 0.38/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.54  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.38/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.54  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.54  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.38/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.54  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.38/0.54                                           $i > $i).
% 0.38/0.54  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.38/0.54  thf(t6_tex_2, conjecture,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( m1_subset_1 @ B @ A ) =>
% 0.38/0.54           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.38/0.54                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.38/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.54    (~( ![A:$i]:
% 0.38/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.54          ( ![B:$i]:
% 0.38/0.54            ( ( m1_subset_1 @ B @ A ) =>
% 0.38/0.54              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.38/0.54                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.38/0.54    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.38/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(dt_k6_domain_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.54       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.54  thf('1', plain,
% 0.38/0.54      (![X62 : $i, X63 : $i]:
% 0.38/0.54         ((v1_xboole_0 @ X62)
% 0.38/0.54          | ~ (m1_subset_1 @ X63 @ X62)
% 0.38/0.54          | (m1_subset_1 @ (k6_domain_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62)))),
% 0.38/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.38/0.54  thf('2', plain,
% 0.38/0.54      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.54        | (v1_xboole_0 @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.54  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.54  thf('4', plain,
% 0.38/0.54      (![X64 : $i, X65 : $i]:
% 0.38/0.54         ((v1_xboole_0 @ X64)
% 0.38/0.54          | ~ (m1_subset_1 @ X65 @ X64)
% 0.38/0.54          | ((k6_domain_1 @ X64 @ X65) = (k1_tarski @ X65)))),
% 0.38/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.54  thf('5', plain,
% 0.38/0.54      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.38/0.54        | (v1_xboole_0 @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.54  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.38/0.54      inference('clc', [status(thm)], ['5', '6'])).
% 0.38/0.54  thf('8', plain,
% 0.38/0.54      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.54        | (v1_xboole_0 @ sk_A))),
% 0.38/0.54      inference('demod', [status(thm)], ['2', '7'])).
% 0.38/0.54  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.54      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.54  thf(cc2_tex_2, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.54           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.38/0.54  thf('11', plain,
% 0.38/0.54      (![X66 : $i, X67 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ X67))
% 0.38/0.54          | ~ (v1_subset_1 @ X66 @ X67)
% 0.38/0.54          | (v1_xboole_0 @ X66)
% 0.38/0.54          | ~ (v1_zfmisc_1 @ X67)
% 0.38/0.54          | (v1_xboole_0 @ X67))),
% 0.38/0.54      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.38/0.54  thf('12', plain,
% 0.38/0.54      (((v1_xboole_0 @ sk_A)
% 0.38/0.54        | ~ (v1_zfmisc_1 @ sk_A)
% 0.38/0.54        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.38/0.54        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.54  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.38/0.54      inference('clc', [status(thm)], ['5', '6'])).
% 0.38/0.54  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.38/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.54  thf('17', plain,
% 0.38/0.54      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.38/0.54      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.38/0.54  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.38/0.54      inference('clc', [status(thm)], ['17', '18'])).
% 0.38/0.54  thf(l13_xboole_0, axiom,
% 0.38/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.54  thf('20', plain,
% 0.38/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.54  thf('21', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.54  thf(t69_enumset1, axiom,
% 0.38/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.54  thf('22', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.38/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.54  thf(t70_enumset1, axiom,
% 0.38/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.54  thf('23', plain,
% 0.38/0.54      (![X2 : $i, X3 : $i]:
% 0.38/0.54         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.38/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.54  thf(t71_enumset1, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i]:
% 0.38/0.54     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.38/0.54  thf('24', plain,
% 0.38/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.54         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 0.38/0.54      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.38/0.54  thf(t72_enumset1, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.54     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.38/0.54  thf('25', plain,
% 0.38/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.54         ((k3_enumset1 @ X7 @ X7 @ X8 @ X9 @ X10)
% 0.38/0.54           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 0.38/0.54      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.38/0.54  thf(t73_enumset1, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.38/0.54     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.38/0.54       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.38/0.54  thf('26', plain,
% 0.38/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.54         ((k4_enumset1 @ X11 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.38/0.54           = (k3_enumset1 @ X11 @ X12 @ X13 @ X14 @ X15))),
% 0.38/0.54      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.38/0.54  thf(t74_enumset1, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.54     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.38/0.54       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.38/0.54  thf('27', plain,
% 0.38/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.54         ((k5_enumset1 @ X16 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.38/0.54           = (k4_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21))),
% 0.38/0.54      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.38/0.54  thf(t75_enumset1, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.38/0.54     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.38/0.54       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.38/0.54  thf('28', plain,
% 0.38/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.54         ((k6_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.38/0.54           = (k5_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.38/0.54      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.38/0.54  thf(d6_enumset1, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.38/0.54     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.38/0.54       ( ![J:$i]:
% 0.38/0.54         ( ( r2_hidden @ J @ I ) <=>
% 0.38/0.54           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.38/0.54                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.38/0.54                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.54  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.38/0.54      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.38/0.54  thf(zf_stmt_2, axiom,
% 0.38/0.54    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.54     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.38/0.54       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.38/0.54         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.38/0.54         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.38/0.54  thf(zf_stmt_3, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.38/0.54     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.38/0.54       ( ![J:$i]:
% 0.38/0.54         ( ( r2_hidden @ J @ I ) <=>
% 0.38/0.54           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.38/0.54  thf('29', plain,
% 0.38/0.54      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 0.38/0.54         X46 : $i, X47 : $i, X48 : $i]:
% 0.38/0.54         ((zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 0.38/0.54          | (r2_hidden @ X39 @ X48)
% 0.38/0.54          | ((X48)
% 0.38/0.54              != (k6_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.54  thf('30', plain,
% 0.38/0.54      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, 
% 0.38/0.54         X46 : $i, X47 : $i]:
% 0.38/0.54         ((r2_hidden @ X39 @ 
% 0.38/0.54           (k6_enumset1 @ X47 @ X46 @ X45 @ X44 @ X43 @ X42 @ X41 @ X40))
% 0.38/0.54          | (zip_tseitin_0 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ 
% 0.38/0.54             X47))),
% 0.38/0.54      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.54  thf('31', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.54         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.38/0.54          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.38/0.54      inference('sup+', [status(thm)], ['28', '30'])).
% 0.38/0.54  thf('32', plain,
% 0.38/0.54      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, 
% 0.38/0.54         X36 : $i, X37 : $i]:
% 0.38/0.54         (((X30) != (X29))
% 0.38/0.54          | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ 
% 0.38/0.54               X29))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.54  thf('33', plain,
% 0.38/0.54      (![X29 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, 
% 0.38/0.54         X37 : $i]:
% 0.38/0.54         ~ (zip_tseitin_0 @ X29 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 @ X29)),
% 0.38/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.54  thf('34', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.54         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.38/0.54      inference('sup-', [status(thm)], ['31', '33'])).
% 0.38/0.54  thf(t7_ordinal1, axiom,
% 0.38/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.54  thf('35', plain,
% 0.38/0.54      (![X60 : $i, X61 : $i]:
% 0.38/0.54         (~ (r2_hidden @ X60 @ X61) | ~ (r1_tarski @ X61 @ X60))),
% 0.38/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.54  thf('36', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.54         ~ (r1_tarski @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)),
% 0.38/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.54  thf('37', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.54         ~ (r1_tarski @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)),
% 0.38/0.54      inference('sup-', [status(thm)], ['27', '36'])).
% 0.38/0.54  thf('38', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.54         ~ (r1_tarski @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X4)),
% 0.38/0.54      inference('sup-', [status(thm)], ['26', '37'])).
% 0.38/0.54  thf('39', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.54         ~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X3)),
% 0.38/0.54      inference('sup-', [status(thm)], ['25', '38'])).
% 0.38/0.54  thf('40', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.54         ~ (r1_tarski @ (k1_enumset1 @ X2 @ X1 @ X0) @ X2)),
% 0.38/0.54      inference('sup-', [status(thm)], ['24', '39'])).
% 0.38/0.54  thf('41', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X1)),
% 0.38/0.54      inference('sup-', [status(thm)], ['23', '40'])).
% 0.38/0.54  thf('42', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.38/0.54      inference('sup-', [status(thm)], ['22', '41'])).
% 0.38/0.54  thf('43', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_B)),
% 0.38/0.54      inference('sup-', [status(thm)], ['21', '42'])).
% 0.38/0.54  thf(t4_subset_1, axiom,
% 0.38/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.54  thf('44', plain,
% 0.38/0.54      (![X51 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X51))),
% 0.38/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.54  thf(t3_subset, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.54  thf('45', plain,
% 0.38/0.54      (![X54 : $i, X55 : $i]:
% 0.38/0.54         ((r1_tarski @ X54 @ X55) | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X55)))),
% 0.38/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.54  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.54  thf('47', plain, ($false), inference('demod', [status(thm)], ['43', '46'])).
% 0.38/0.54  
% 0.38/0.54  % SZS output end Refutation
% 0.38/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
