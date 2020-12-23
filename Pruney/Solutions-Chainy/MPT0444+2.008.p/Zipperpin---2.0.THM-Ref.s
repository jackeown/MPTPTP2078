%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P09cDI3E6m

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:46 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   69 (  95 expanded)
%              Number of leaves         :   27 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  496 ( 745 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X14 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('7',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X42 ) @ X43 )
      | ~ ( r2_hidden @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k2_relat_1 @ X47 ) @ ( k2_relat_1 @ X46 ) )
      | ~ ( r1_tarski @ X47 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_relat_1 @ X44 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','15'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k2_relat_1 @ X47 ) @ ( k2_relat_1 @ X46 ) )
      | ~ ( r1_tarski @ X47 @ X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('23',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( v1_relat_1 @ X44 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','26'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('29',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','31'])).

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

thf('33',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['37','38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P09cDI3E6m
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 209 iterations in 0.093s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.55  thf(t70_enumset1, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      (![X17 : $i, X18 : $i]:
% 0.38/0.55         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.38/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.55  thf(d1_enumset1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.55       ( ![E:$i]:
% 0.38/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.38/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.55  thf(zf_stmt_1, axiom,
% 0.38/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.38/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.38/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_2, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.55       ( ![E:$i]:
% 0.38/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.55         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.38/0.55          | (r2_hidden @ X10 @ X14)
% 0.38/0.55          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.38/0.55         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.38/0.55          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.38/0.55      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['0', '2'])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.55         (((X6) != (X7)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X7 @ X7 @ X8 @ X5)),
% 0.38/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['3', '5'])).
% 0.38/0.55  thf(t4_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (![X42 : $i, X43 : $i]:
% 0.38/0.55         ((r1_tarski @ (k1_setfam_1 @ X42) @ X43) | ~ (r2_hidden @ X43 @ X42))),
% 0.38/0.55      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf(t25_relat_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( v1_relat_1 @ B ) =>
% 0.38/0.55           ( ( r1_tarski @ A @ B ) =>
% 0.38/0.55             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.38/0.55               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (![X46 : $i, X47 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X46)
% 0.38/0.55          | (r1_tarski @ (k2_relat_1 @ X47) @ (k2_relat_1 @ X46))
% 0.38/0.55          | ~ (r1_tarski @ X47 @ X46)
% 0.38/0.55          | ~ (v1_relat_1 @ X47))),
% 0.38/0.55      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.55  thf('10', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.38/0.55             (k2_relat_1 @ X0))
% 0.38/0.55          | ~ (v1_relat_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf(t3_subset, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (![X39 : $i, X41 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 0.38/0.55          (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.55  thf(cc2_relat_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (![X44 : $i, X45 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.38/0.55          | (v1_relat_1 @ X44)
% 0.38/0.55          | ~ (v1_relat_1 @ X45))),
% 0.38/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.38/0.55             (k2_relat_1 @ X0)))),
% 0.38/0.55      inference('clc', [status(thm)], ['10', '15'])).
% 0.38/0.55  thf(t17_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.38/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.55  thf(t12_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X37 : $i, X38 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.38/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X46 : $i, X47 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X46)
% 0.38/0.55          | (r1_tarski @ (k2_relat_1 @ X47) @ (k2_relat_1 @ X46))
% 0.38/0.55          | ~ (r1_tarski @ X47 @ X46)
% 0.38/0.55          | ~ (v1_relat_1 @ X47))),
% 0.38/0.55      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.55  thf('21', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.38/0.55             (k2_relat_1 @ X0))
% 0.38/0.55          | ~ (v1_relat_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.38/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X39 : $i, X41 : $i]:
% 0.38/0.55         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.55  thf('24', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ 
% 0.38/0.55          (k1_zfmisc_1 @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X44 : $i, X45 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.38/0.55          | (v1_relat_1 @ X44)
% 0.38/0.55          | ~ (v1_relat_1 @ X45))),
% 0.38/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (v1_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.38/0.55             (k2_relat_1 @ X0)))),
% 0.38/0.55      inference('clc', [status(thm)], ['21', '26'])).
% 0.38/0.55  thf(t19_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.38/0.55       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X2 @ X3)
% 0.38/0.55          | ~ (r1_tarski @ X2 @ X4)
% 0.38/0.55          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X37 : $i, X38 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X2 @ X3)
% 0.38/0.55          | ~ (r1_tarski @ X2 @ X4)
% 0.38/0.55          | (r1_tarski @ X2 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X4))))),
% 0.38/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ 
% 0.38/0.55             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X2)))
% 0.38/0.55          | ~ (r1_tarski @ 
% 0.38/0.55               (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))) @ X2))),
% 0.38/0.55      inference('sup-', [status(thm)], ['27', '30'])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         (~ (v1_relat_1 @ X0)
% 0.38/0.55          | (r1_tarski @ 
% 0.38/0.55             (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ 
% 0.38/0.55             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 0.38/0.55          | ~ (v1_relat_1 @ X1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['16', '31'])).
% 0.38/0.55  thf(t27_relat_1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( v1_relat_1 @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( v1_relat_1 @ B ) =>
% 0.38/0.55           ( r1_tarski @
% 0.38/0.55             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.38/0.55             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_3, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( v1_relat_1 @ A ) =>
% 0.38/0.55          ( ![B:$i]:
% 0.38/0.55            ( ( v1_relat_1 @ B ) =>
% 0.38/0.55              ( r1_tarski @
% 0.38/0.55                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.38/0.55                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.38/0.55          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X37 : $i, X38 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (![X37 : $i, X38 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (~ (r1_tarski @ 
% 0.38/0.55          (k2_relat_1 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))) @ 
% 0.38/0.55          (k1_setfam_1 @ 
% 0.38/0.55           (k2_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))))),
% 0.38/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.38/0.55  thf('37', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['32', '36'])).
% 0.38/0.55  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.55  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.55  thf('40', plain, ($false),
% 0.38/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
