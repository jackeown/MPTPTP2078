%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qbak50MMYh

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:40 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 110 expanded)
%              Number of leaves         :   39 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  645 ( 872 expanded)
%              Number of equality atoms :   49 (  52 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X59: $i,X60: $i] :
      ( ( v1_xboole_0 @ X59 )
      | ~ ( m1_subset_1 @ X60 @ X59 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X59 @ X60 ) @ ( k1_zfmisc_1 @ X59 ) ) ) ),
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
    ! [X61: $i,X62: $i] :
      ( ( v1_xboole_0 @ X61 )
      | ~ ( m1_subset_1 @ X62 @ X61 )
      | ( ( k6_domain_1 @ X61 @ X62 )
        = ( k1_tarski @ X62 ) ) ) ),
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
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X64 ) )
      | ~ ( v1_subset_1 @ X63 @ X64 )
      | ( v1_xboole_0 @ X63 )
      | ~ ( v1_zfmisc_1 @ X64 )
      | ( v1_xboole_0 @ X64 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X3 @ X3 @ X4 )
      = ( k2_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X5 @ X5 @ X6 @ X7 )
      = ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k3_enumset1 @ X8 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k4_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k5_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k6_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k5_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
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

thf('31',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      | ( r2_hidden @ X45 @ X54 )
      | ( X54
       != ( k6_enumset1 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( r2_hidden @ X45 @ ( k6_enumset1 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46 ) )
      | ( zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X36 != X35 )
      | ~ ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    ! [X35: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ~ ( zip_tseitin_0 @ X35 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X35 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r2_hidden @ X0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r2_hidden @ X5 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r2_hidden @ X4 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','41'])).

thf('43',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['23','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X31: $i] :
      ( ( k2_zfmisc_1 @ X31 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X33: $i,X34: $i] :
      ~ ( r2_hidden @ X33 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('sup-',[status(thm)],['43','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qbak50MMYh
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 161 iterations in 0.103s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.37/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.37/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.37/0.56                                           $i > $i).
% 0.37/0.56  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > 
% 0.37/0.56                                               $i > $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(t6_tex_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ A ) =>
% 0.37/0.56           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.37/0.56                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( m1_subset_1 @ B @ A ) =>
% 0.37/0.56              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.37/0.56                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.37/0.56  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_k6_domain_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.56       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X59 : $i, X60 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X59)
% 0.37/0.56          | ~ (m1_subset_1 @ X60 @ X59)
% 0.37/0.56          | (m1_subset_1 @ (k6_domain_1 @ X59 @ X60) @ (k1_zfmisc_1 @ X59)))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.56        | (v1_xboole_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.37/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X61 : $i, X62 : $i]:
% 0.37/0.56         ((v1_xboole_0 @ X61)
% 0.37/0.56          | ~ (m1_subset_1 @ X62 @ X61)
% 0.37/0.56          | ((k6_domain_1 @ X61 @ X62) = (k1_tarski @ X62)))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.37/0.56        | (v1_xboole_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.56  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('7', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.56        | (v1_xboole_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['2', '7'])).
% 0.37/0.56  thf('9', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('10', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf(cc2_tex_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.56           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X63 : $i, X64 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X64))
% 0.37/0.56          | ~ (v1_subset_1 @ X63 @ X64)
% 0.37/0.56          | (v1_xboole_0 @ X63)
% 0.37/0.56          | ~ (v1_zfmisc_1 @ X64)
% 0.37/0.56          | (v1_xboole_0 @ X64))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_A)
% 0.37/0.56        | ~ (v1_zfmisc_1 @ sk_A)
% 0.37/0.56        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.37/0.56        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('13', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('14', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['14', '15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '13', '16'])).
% 0.37/0.56  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.37/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.56  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.56  thf(t8_boole, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t8_boole])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain, (((k1_xboole_0) = (k1_tarski @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['19', '22'])).
% 0.37/0.56  thf(t69_enumset1, axiom,
% 0.37/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.56  thf('24', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.37/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.56  thf(t70_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X3 : $i, X4 : $i]:
% 0.37/0.56         ((k1_enumset1 @ X3 @ X3 @ X4) = (k2_tarski @ X3 @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.56  thf(t71_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.56         ((k2_enumset1 @ X5 @ X5 @ X6 @ X7) = (k1_enumset1 @ X5 @ X6 @ X7))),
% 0.37/0.56      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.37/0.56  thf(t72_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.56     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.56         ((k3_enumset1 @ X8 @ X8 @ X9 @ X10 @ X11)
% 0.37/0.56           = (k2_enumset1 @ X8 @ X9 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.37/0.56  thf(t73_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.56     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.37/0.56       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.56         ((k4_enumset1 @ X12 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.37/0.56           = (k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.37/0.56  thf(t74_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.56     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.37/0.56       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.56         ((k5_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.37/0.56           = (k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.37/0.56  thf(t75_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.37/0.56     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.37/0.56       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.56         ((k6_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.37/0.56           = (k5_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 0.37/0.56      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.37/0.56  thf(d6_enumset1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.37/0.56     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.37/0.56       ( ![J:$i]:
% 0.37/0.56         ( ( r2_hidden @ J @ I ) <=>
% 0.37/0.56           ( ~( ( ( J ) != ( H ) ) & ( ( J ) != ( G ) ) & ( ( J ) != ( F ) ) & 
% 0.37/0.56                ( ( J ) != ( E ) ) & ( ( J ) != ( D ) ) & ( ( J ) != ( C ) ) & 
% 0.37/0.56                ( ( J ) != ( B ) ) & ( ( J ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_1, type, zip_tseitin_0 :
% 0.37/0.56      $i > $i > $i > $i > $i > $i > $i > $i > $i > $o).
% 0.37/0.56  thf(zf_stmt_2, axiom,
% 0.37/0.56    (![J:$i,H:$i,G:$i,F:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.37/0.56     ( ( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) <=>
% 0.37/0.56       ( ( ( J ) != ( A ) ) & ( ( J ) != ( B ) ) & ( ( J ) != ( C ) ) & 
% 0.37/0.56         ( ( J ) != ( D ) ) & ( ( J ) != ( E ) ) & ( ( J ) != ( F ) ) & 
% 0.37/0.56         ( ( J ) != ( G ) ) & ( ( J ) != ( H ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_3, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i,I:$i]:
% 0.37/0.56     ( ( ( I ) = ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) <=>
% 0.37/0.56       ( ![J:$i]:
% 0.37/0.56         ( ( r2_hidden @ J @ I ) <=>
% 0.37/0.56           ( ~( zip_tseitin_0 @ J @ H @ G @ F @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, 
% 0.37/0.56         X52 : $i, X53 : $i, X54 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 0.37/0.56          | (r2_hidden @ X45 @ X54)
% 0.37/0.56          | ((X54)
% 0.37/0.56              != (k6_enumset1 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, 
% 0.37/0.56         X52 : $i, X53 : $i]:
% 0.37/0.56         ((r2_hidden @ X45 @ 
% 0.37/0.56           (k6_enumset1 @ X53 @ X52 @ X51 @ X50 @ X49 @ X48 @ X47 @ X46))
% 0.37/0.56          | (zip_tseitin_0 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ 
% 0.37/0.56             X53))),
% 0.37/0.56      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.56         ((r2_hidden @ X7 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.37/0.56          | (zip_tseitin_0 @ X7 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6))),
% 0.37/0.56      inference('sup+', [status(thm)], ['30', '32'])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 0.37/0.56         X42 : $i, X43 : $i]:
% 0.37/0.56         (((X36) != (X35))
% 0.37/0.56          | ~ (zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ 
% 0.37/0.56               X35))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X35 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, 
% 0.37/0.56         X43 : $i]:
% 0.37/0.56         ~ (zip_tseitin_0 @ X35 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X35)),
% 0.37/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.37/0.56         (r2_hidden @ X0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6))),
% 0.37/0.56      inference('sup-', [status(thm)], ['33', '35'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.37/0.56         (r2_hidden @ X5 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['29', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         (r2_hidden @ X4 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['28', '37'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.56         (r2_hidden @ X3 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['27', '38'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['26', '39'])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['25', '40'])).
% 0.37/0.56  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['24', '41'])).
% 0.37/0.56  thf('43', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.37/0.56      inference('sup+', [status(thm)], ['23', '42'])).
% 0.37/0.56  thf(t113_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X31 : $i, X32 : $i]:
% 0.37/0.56         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 0.37/0.56          | ((X32) != (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      (![X31 : $i]: ((k2_zfmisc_1 @ X31 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.56  thf(t152_zfmisc_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X33 : $i, X34 : $i]: ~ (r2_hidden @ X33 @ (k2_zfmisc_1 @ X33 @ X34))),
% 0.37/0.56      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.37/0.56  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain, ($false), inference('sup-', [status(thm)], ['43', '47'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
