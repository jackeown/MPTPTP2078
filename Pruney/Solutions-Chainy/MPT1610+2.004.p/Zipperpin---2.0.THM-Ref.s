%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sZyLgwq5cv

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:13 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 132 expanded)
%              Number of leaves         :   34 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  468 ( 726 expanded)
%              Number of equality atoms :   68 ( 108 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t18_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow_1])).

thf('0',plain,(
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X9 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X42 )
      | ( X42
       != ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r2_hidden @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X53: $i] :
      ( ( k9_setfam_1 @ X53 )
      = ( k1_zfmisc_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r2_hidden @ X40 @ ( k9_setfam_1 @ X41 ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X54: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X54 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X54 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X55: $i] :
      ( ( k3_yellow_1 @ X55 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('13',plain,(
    ! [X48: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('14',plain,(
    ! [X53: $i] :
      ( ( k9_setfam_1 @ X53 )
      = ( k1_zfmisc_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('15',plain,(
    ! [X48: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X48 ) )
      = X48 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('17',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('19',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('20',plain,(
    ! [X53: $i] :
      ( ( k9_setfam_1 @ X53 )
      = ( k1_zfmisc_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('21',plain,
    ( ( k9_setfam_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('23',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46 != X45 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X46 ) @ ( k1_tarski @ X45 ) )
       != ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('24',plain,(
    ! [X45: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X45 ) @ ( k1_tarski @ X45 ) )
     != ( k1_tarski @ X45 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X45: $i] :
      ( ( k6_subset_1 @ ( k1_tarski @ X45 ) @ ( k1_tarski @ X45 ) )
     != ( k1_tarski @ X45 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k6_subset_1 @ X49 @ X50 )
      = ( k4_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X11: $i] :
      ( ( k6_subset_1 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X45: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X45 ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_setfam_1 @ ( k3_tarski @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','40'])).

thf('42',plain,(
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r2_hidden @ X40 @ ( k9_setfam_1 @ X41 ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X54: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X54 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X54 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ k1_xboole_0 ) )
    | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ k1_xboole_0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X55: $i] :
      ( ( k3_yellow_1 @ X55 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k9_setfam_1 @ k1_xboole_0 ) )
    | ( ( k3_yellow_0 @ ( k3_yellow_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ ( k9_setfam_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf('54',plain,
    ( ( k3_yellow_0 @ ( k3_yellow_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','44','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sZyLgwq5cv
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 407 iterations in 0.195s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.45/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.64  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.45/0.64  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.45/0.64  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(t18_yellow_1, conjecture,
% 0.45/0.64    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.45/0.64  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t61_xboole_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X9 : $i]: ((r2_xboole_0 @ k1_xboole_0 @ X9) | ((X9) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.45/0.64  thf(d8_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.45/0.64       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.45/0.64      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf(d1_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.45/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.45/0.64         (~ (r1_tarski @ X40 @ X41)
% 0.45/0.64          | (r2_hidden @ X40 @ X42)
% 0.45/0.64          | ((X42) != (k1_zfmisc_1 @ X41)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X40 : $i, X41 : $i]:
% 0.45/0.64         ((r2_hidden @ X40 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X40 @ X41))),
% 0.45/0.64      inference('simplify', [status(thm)], ['4'])).
% 0.45/0.64  thf(redefinition_k9_setfam_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.64  thf('6', plain, (![X53 : $i]: ((k9_setfam_1 @ X53) = (k1_zfmisc_1 @ X53))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X40 : $i, X41 : $i]:
% 0.45/0.64         ((r2_hidden @ X40 @ (k9_setfam_1 @ X41)) | ~ (r1_tarski @ X40 @ X41))),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((X0) = (k1_xboole_0))
% 0.45/0.64          | (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['3', '7'])).
% 0.45/0.64  thf(t13_yellow_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.64       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.45/0.64         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X54 : $i]:
% 0.45/0.64         (~ (r2_hidden @ k1_xboole_0 @ X54)
% 0.45/0.64          | ((k3_yellow_0 @ (k2_yellow_1 @ X54)) = (k1_xboole_0))
% 0.45/0.64          | (v1_xboole_0 @ X54))),
% 0.45/0.64      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((X0) = (k1_xboole_0))
% 0.45/0.64          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.45/0.64          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf(t4_yellow_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X55 : $i]: ((k3_yellow_1 @ X55) = (k2_yellow_1 @ (k9_setfam_1 @ X55)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((X0) = (k1_xboole_0))
% 0.45/0.64          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.45/0.64          | ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['10', '11'])).
% 0.45/0.64  thf(t99_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.45/0.64  thf('13', plain, (![X48 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X48)) = (X48))),
% 0.45/0.64      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.45/0.64  thf('14', plain, (![X53 : $i]: ((k9_setfam_1 @ X53) = (k1_zfmisc_1 @ X53))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.45/0.64  thf('15', plain, (![X48 : $i]: ((k3_tarski @ (k9_setfam_1 @ X48)) = (X48))),
% 0.45/0.64      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.64  thf(t6_boole, axiom,
% 0.45/0.64    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X10 : $i]: (((X10) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.64  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.45/0.64  thf('17', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X0 : $i]: (((k3_tarski @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.64  thf(t1_zfmisc_1, axiom,
% 0.45/0.64    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.45/0.64  thf('19', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.45/0.64  thf('20', plain, (![X53 : $i]: ((k9_setfam_1 @ X53) = (k1_zfmisc_1 @ X53))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.45/0.64  thf('21', plain, (((k9_setfam_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X10 : $i]: (((X10) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.64  thf(t20_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.64         ( k1_tarski @ A ) ) <=>
% 0.45/0.64       ( ( A ) != ( B ) ) ))).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X45 : $i, X46 : $i]:
% 0.45/0.64         (((X46) != (X45))
% 0.45/0.64          | ((k4_xboole_0 @ (k1_tarski @ X46) @ (k1_tarski @ X45))
% 0.45/0.64              != (k1_tarski @ X46)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (![X45 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ (k1_tarski @ X45) @ (k1_tarski @ X45))
% 0.45/0.64           != (k1_tarski @ X45))),
% 0.45/0.64      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.64  thf(redefinition_k6_subset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      (![X49 : $i, X50 : $i]:
% 0.45/0.64         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X45 : $i]:
% 0.45/0.64         ((k6_subset_1 @ (k1_tarski @ X45) @ (k1_tarski @ X45))
% 0.45/0.64           != (k1_tarski @ X45))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf(t92_xboole_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf('27', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.45/0.64  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.64  thf('28', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.45/0.64      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.64  thf(t100_xboole_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.64  thf('29', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         ((k4_xboole_0 @ X7 @ X8)
% 0.45/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X49 : $i, X50 : $i]:
% 0.45/0.64         ((k6_subset_1 @ X49 @ X50) = (k4_xboole_0 @ X49 @ X50))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         ((k6_subset_1 @ X7 @ X8)
% 0.45/0.64           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.64      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['28', '31'])).
% 0.45/0.64  thf('33', plain, (![X11 : $i]: ((k6_subset_1 @ X11 @ X11) = (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['27', '32'])).
% 0.45/0.64  thf('34', plain, (![X45 : $i]: ((k1_xboole_0) != (k1_tarski @ X45))),
% 0.45/0.64      inference('demod', [status(thm)], ['26', '33'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]: (((X0) != (k1_tarski @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['22', '34'])).
% 0.45/0.64  thf('36', plain, (![X1 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X1))),
% 0.45/0.64      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.64  thf('37', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['21', '36'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k9_setfam_1 @ (k3_tarski @ X0)))
% 0.45/0.64          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['18', '37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.45/0.64          | ~ (v1_xboole_0 @ (k9_setfam_1 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '38'])).
% 0.45/0.64  thf('40', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['39'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))
% 0.45/0.64          | ((X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('clc', [status(thm)], ['12', '40'])).
% 0.45/0.64  thf('42', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('43', plain,
% 0.45/0.64      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.64  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.45/0.64  thf(d10_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('46', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.45/0.64      inference('simplify', [status(thm)], ['45'])).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X40 : $i, X41 : $i]:
% 0.45/0.64         ((r2_hidden @ X40 @ (k9_setfam_1 @ X41)) | ~ (r1_tarski @ X40 @ X41))),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.64  thf('48', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain,
% 0.45/0.64      (![X54 : $i]:
% 0.45/0.64         (~ (r2_hidden @ k1_xboole_0 @ X54)
% 0.45/0.64          | ((k3_yellow_0 @ (k2_yellow_1 @ X54)) = (k1_xboole_0))
% 0.45/0.64          | (v1_xboole_0 @ X54))),
% 0.45/0.64      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k9_setfam_1 @ k1_xboole_0))
% 0.45/0.64        | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ k1_xboole_0)))
% 0.45/0.64            = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X55 : $i]: ((k3_yellow_1 @ X55) = (k2_yellow_1 @ (k9_setfam_1 @ X55)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.45/0.64  thf('52', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k9_setfam_1 @ k1_xboole_0))
% 0.45/0.64        | ((k3_yellow_0 @ (k3_yellow_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.45/0.64  thf('53', plain, (~ (v1_xboole_0 @ (k9_setfam_1 @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['21', '36'])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (((k3_yellow_0 @ (k3_yellow_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.45/0.64      inference('clc', [status(thm)], ['52', '53'])).
% 0.45/0.64  thf('55', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['0', '44', '54'])).
% 0.45/0.64  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.50/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
