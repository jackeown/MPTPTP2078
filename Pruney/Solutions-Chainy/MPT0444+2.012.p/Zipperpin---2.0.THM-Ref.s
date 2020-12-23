%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HXm9AwH4XC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:47 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 109 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  589 ( 923 expanded)
%              Number of equality atoms :   25 (  44 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X32 @ X38 )
      | ( X38
       != ( k3_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X32 @ ( k3_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X26 != X27 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 @ X30 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
    ! [X25: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X27 @ X27 @ X28 @ X29 @ X30 @ X25 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X3 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('11',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X46 ) @ X47 )
      | ~ ( r2_hidden @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k2_relat_1 @ X51 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ X51 @ X50 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','19'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k2_relat_1 @ X51 ) @ ( k2_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ X51 @ X50 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('27',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','30'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['41','42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HXm9AwH4XC
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:43:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.64/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.84  % Solved by: fo/fo7.sh
% 0.64/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.84  % done 469 iterations in 0.343s
% 0.64/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.84  % SZS output start Refutation
% 0.64/0.84  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.64/0.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 0.64/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.64/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.84  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.64/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.64/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.64/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.84  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.64/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.64/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.64/0.84  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.64/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.64/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.84  thf(t70_enumset1, axiom,
% 0.64/0.84    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.64/0.84  thf('0', plain,
% 0.64/0.84      (![X5 : $i, X6 : $i]:
% 0.64/0.84         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.64/0.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.64/0.84  thf(t71_enumset1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i]:
% 0.64/0.84     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.64/0.84  thf('1', plain,
% 0.64/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.64/0.84         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 0.64/0.84      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.64/0.84  thf(t72_enumset1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.84     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.64/0.84  thf('2', plain,
% 0.64/0.84      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.64/0.84         ((k3_enumset1 @ X10 @ X10 @ X11 @ X12 @ X13)
% 0.64/0.84           = (k2_enumset1 @ X10 @ X11 @ X12 @ X13))),
% 0.64/0.84      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.64/0.84  thf(d3_enumset1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.64/0.84     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.64/0.84       ( ![G:$i]:
% 0.64/0.84         ( ( r2_hidden @ G @ F ) <=>
% 0.64/0.84           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 0.64/0.84                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 0.64/0.84  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 0.64/0.84  thf(zf_stmt_1, axiom,
% 0.64/0.84    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.64/0.84     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 0.64/0.84       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 0.64/0.84         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 0.64/0.84  thf(zf_stmt_2, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.64/0.84     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 0.64/0.84       ( ![G:$i]:
% 0.64/0.84         ( ( r2_hidden @ G @ F ) <=>
% 0.64/0.84           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 0.64/0.84  thf('3', plain,
% 0.64/0.84      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.64/0.84         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 0.64/0.84          | (r2_hidden @ X32 @ X38)
% 0.64/0.84          | ((X38) != (k3_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33)))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.64/0.84  thf('4', plain,
% 0.64/0.84      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.64/0.84         ((r2_hidden @ X32 @ (k3_enumset1 @ X37 @ X36 @ X35 @ X34 @ X33))
% 0.64/0.84          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 0.64/0.84      inference('simplify', [status(thm)], ['3'])).
% 0.64/0.84  thf('5', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.64/0.84         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.64/0.84          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 0.64/0.84      inference('sup+', [status(thm)], ['2', '4'])).
% 0.64/0.84  thf('6', plain,
% 0.64/0.84      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.64/0.84         (((X26) != (X27))
% 0.64/0.84          | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 @ X30 @ X25))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.64/0.84  thf('7', plain,
% 0.64/0.84      (![X25 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.64/0.84         ~ (zip_tseitin_0 @ X27 @ X27 @ X28 @ X29 @ X30 @ X25)),
% 0.64/0.84      inference('simplify', [status(thm)], ['6'])).
% 0.64/0.84  thf('8', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.64/0.84         (r2_hidden @ X3 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 0.64/0.84      inference('sup-', [status(thm)], ['5', '7'])).
% 0.64/0.84  thf('9', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.84         (r2_hidden @ X0 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.64/0.84      inference('sup+', [status(thm)], ['1', '8'])).
% 0.64/0.84  thf('10', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.64/0.84      inference('sup+', [status(thm)], ['0', '9'])).
% 0.64/0.84  thf(t4_setfam_1, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.64/0.84  thf('11', plain,
% 0.64/0.84      (![X46 : $i, X47 : $i]:
% 0.64/0.84         ((r1_tarski @ (k1_setfam_1 @ X46) @ X47) | ~ (r2_hidden @ X47 @ X46))),
% 0.64/0.84      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.64/0.84  thf('12', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.64/0.84      inference('sup-', [status(thm)], ['10', '11'])).
% 0.64/0.84  thf(t25_relat_1, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( v1_relat_1 @ A ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( v1_relat_1 @ B ) =>
% 0.64/0.84           ( ( r1_tarski @ A @ B ) =>
% 0.64/0.84             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.64/0.84               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.64/0.84  thf('13', plain,
% 0.64/0.84      (![X50 : $i, X51 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ X50)
% 0.64/0.84          | (r1_tarski @ (k2_relat_1 @ X51) @ (k2_relat_1 @ X50))
% 0.64/0.84          | ~ (r1_tarski @ X51 @ X50)
% 0.64/0.84          | ~ (v1_relat_1 @ X51))),
% 0.64/0.84      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.64/0.84  thf('14', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.64/0.84          | (r1_tarski @ 
% 0.64/0.84             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.64/0.84             (k2_relat_1 @ X0))
% 0.64/0.84          | ~ (v1_relat_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.64/0.84  thf('15', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.64/0.84      inference('sup-', [status(thm)], ['10', '11'])).
% 0.64/0.84  thf(t3_subset, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.64/0.84  thf('16', plain,
% 0.64/0.84      (![X43 : $i, X45 : $i]:
% 0.64/0.84         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 0.64/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.84  thf('17', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.64/0.84          (k1_zfmisc_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['15', '16'])).
% 0.64/0.84  thf(cc2_relat_1, axiom,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( v1_relat_1 @ A ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.64/0.84  thf('18', plain,
% 0.64/0.84      (![X48 : $i, X49 : $i]:
% 0.64/0.84         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 0.64/0.84          | (v1_relat_1 @ X48)
% 0.64/0.84          | ~ (v1_relat_1 @ X49))),
% 0.64/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.64/0.84  thf('19', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ X0)
% 0.64/0.84          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.64/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.64/0.84  thf('20', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ X0)
% 0.64/0.84          | (r1_tarski @ 
% 0.64/0.84             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.64/0.84             (k2_relat_1 @ X0)))),
% 0.64/0.84      inference('clc', [status(thm)], ['14', '19'])).
% 0.64/0.84  thf(t17_xboole_1, axiom,
% 0.64/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.64/0.84  thf('21', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.64/0.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.64/0.84  thf(t12_setfam_1, axiom,
% 0.64/0.84    (![A:$i,B:$i]:
% 0.64/0.84     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.64/0.84  thf('22', plain,
% 0.64/0.84      (![X41 : $i, X42 : $i]:
% 0.64/0.84         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.64/0.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.64/0.84  thf('23', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.64/0.84      inference('demod', [status(thm)], ['21', '22'])).
% 0.64/0.84  thf('24', plain,
% 0.64/0.84      (![X50 : $i, X51 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ X50)
% 0.64/0.84          | (r1_tarski @ (k2_relat_1 @ X51) @ (k2_relat_1 @ X50))
% 0.64/0.84          | ~ (r1_tarski @ X51 @ X50)
% 0.64/0.84          | ~ (v1_relat_1 @ X51))),
% 0.64/0.84      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.64/0.84  thf('25', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.64/0.84          | (r1_tarski @ 
% 0.64/0.84             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.64/0.84             (k2_relat_1 @ X0))
% 0.64/0.84          | ~ (v1_relat_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['23', '24'])).
% 0.64/0.84  thf('26', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.64/0.84      inference('demod', [status(thm)], ['21', '22'])).
% 0.64/0.84  thf('27', plain,
% 0.64/0.84      (![X43 : $i, X45 : $i]:
% 0.64/0.84         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 0.64/0.84      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.84  thf('28', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.64/0.84          (k1_zfmisc_1 @ X0))),
% 0.64/0.84      inference('sup-', [status(thm)], ['26', '27'])).
% 0.64/0.84  thf('29', plain,
% 0.64/0.84      (![X48 : $i, X49 : $i]:
% 0.64/0.84         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 0.64/0.84          | (v1_relat_1 @ X48)
% 0.64/0.84          | ~ (v1_relat_1 @ X49))),
% 0.64/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.64/0.84  thf('30', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ X0)
% 0.64/0.84          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.64/0.84      inference('sup-', [status(thm)], ['28', '29'])).
% 0.64/0.84  thf('31', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ X0)
% 0.64/0.84          | (r1_tarski @ 
% 0.64/0.84             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.64/0.84             (k2_relat_1 @ X0)))),
% 0.64/0.84      inference('clc', [status(thm)], ['25', '30'])).
% 0.64/0.84  thf(t19_xboole_1, axiom,
% 0.64/0.84    (![A:$i,B:$i,C:$i]:
% 0.64/0.84     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.64/0.84       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.64/0.84  thf('32', plain,
% 0.64/0.84      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.64/0.84         (~ (r1_tarski @ X2 @ X3)
% 0.64/0.84          | ~ (r1_tarski @ X2 @ X4)
% 0.64/0.84          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.64/0.84      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.64/0.84  thf('33', plain,
% 0.64/0.84      (![X41 : $i, X42 : $i]:
% 0.64/0.84         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.64/0.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.64/0.84  thf('34', plain,
% 0.64/0.84      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.64/0.84         (~ (r1_tarski @ X2 @ X3)
% 0.64/0.84          | ~ (r1_tarski @ X2 @ X4)
% 0.64/0.84          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.64/0.84      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.84  thf('35', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ X0)
% 0.64/0.84          | (r1_tarski @ 
% 0.64/0.84             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.64/0.84             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.64/0.84          | ~ (r1_tarski @ 
% 0.64/0.84               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.64/0.84      inference('sup-', [status(thm)], ['31', '34'])).
% 0.64/0.84  thf('36', plain,
% 0.64/0.84      (![X0 : $i, X1 : $i]:
% 0.64/0.84         (~ (v1_relat_1 @ X0)
% 0.64/0.84          | (r1_tarski @ 
% 0.64/0.84             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.64/0.84             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.64/0.84          | ~ (v1_relat_1 @ X1))),
% 0.64/0.84      inference('sup-', [status(thm)], ['20', '35'])).
% 0.64/0.84  thf(t27_relat_1, conjecture,
% 0.64/0.84    (![A:$i]:
% 0.64/0.84     ( ( v1_relat_1 @ A ) =>
% 0.64/0.84       ( ![B:$i]:
% 0.64/0.84         ( ( v1_relat_1 @ B ) =>
% 0.64/0.84           ( r1_tarski @
% 0.64/0.84             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.64/0.84             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.64/0.84  thf(zf_stmt_3, negated_conjecture,
% 0.64/0.84    (~( ![A:$i]:
% 0.64/0.84        ( ( v1_relat_1 @ A ) =>
% 0.64/0.84          ( ![B:$i]:
% 0.64/0.84            ( ( v1_relat_1 @ B ) =>
% 0.64/0.84              ( r1_tarski @
% 0.64/0.84                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.64/0.84                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.64/0.84    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.64/0.84  thf('37', plain,
% 0.64/0.84      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.64/0.84          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.64/0.84  thf('38', plain,
% 0.64/0.84      (![X41 : $i, X42 : $i]:
% 0.64/0.84         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.64/0.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.64/0.84  thf('39', plain,
% 0.64/0.84      (![X41 : $i, X42 : $i]:
% 0.64/0.84         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.64/0.84      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.64/0.84  thf('40', plain,
% 0.64/0.84      (~ (r1_tarski @ 
% 0.64/0.84          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.64/0.84          (k1_setfam_1 @ 
% 0.64/0.84           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.64/0.84      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.64/0.84  thf('41', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.64/0.84      inference('sup-', [status(thm)], ['36', '40'])).
% 0.64/0.84  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.64/0.84  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.64/0.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.64/0.84  thf('44', plain, ($false),
% 0.64/0.84      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.64/0.84  
% 0.64/0.84  % SZS output end Refutation
% 0.64/0.84  
% 0.64/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
