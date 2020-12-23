%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HOFZnYbDs8

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 170 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  540 (1381 expanded)
%              Number of equality atoms :   52 ( 134 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X45: $i,X48: $i] :
      ( ( X48
        = ( k1_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X48 @ X45 ) @ ( sk_D @ X48 @ X45 ) ) @ X45 )
      | ( r2_hidden @ ( sk_C_1 @ X48 @ X45 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X6 ) ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('11',plain,(
    ! [X2: $i] :
      ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('14',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('22',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X53 ) @ X54 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('24',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X53 ) @ X54 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X52: $i] :
      ( ( ( k1_relat_1 @ X52 )
       != k1_xboole_0 )
      | ( X52 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('30',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('39',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','37','38'])).

thf('40',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','39'])).

thf('41',plain,(
    ! [X53: $i,X54: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X53 ) @ X54 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('50',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','37'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['49','50'])).

thf('52',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HOFZnYbDs8
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 82 iterations in 0.050s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(d4_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X45 : $i, X48 : $i]:
% 0.21/0.52         (((X48) = (k1_relat_1 @ X45))
% 0.21/0.52          | (r2_hidden @ 
% 0.21/0.52             (k4_tarski @ (sk_C_1 @ X48 @ X45) @ (sk_D @ X48 @ X45)) @ X45)
% 0.21/0.52          | (r2_hidden @ (sk_C_1 @ X48 @ X45) @ X48))),
% 0.21/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.52  thf(t79_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.21/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.52  thf(d7_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.52  thf(t12_setfam_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X41 : $i, X42 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (k1_xboole_0))
% 0.21/0.52          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 0.21/0.52           = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.52  thf(t4_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.21/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X41 : $i, X42 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X5 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X6)))
% 0.21/0.52          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 0.21/0.52          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.21/0.52      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.52  thf('11', plain, (![X2 : $i]: ~ (r2_hidden @ X2 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '11'])).
% 0.21/0.52  thf('13', plain, (![X2 : $i]: ~ (r2_hidden @ X2 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('14', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf(t95_relat_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( v1_relat_1 @ B ) =>
% 0.21/0.52          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.52        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.52         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.52        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.21/0.52       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf(dt_k7_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X50 : $i, X51 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k7_relat_1 @ X50 @ X51)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_setfam_1 @ (k2_tarski @ X0 @ X1)) = (k1_xboole_0))
% 0.21/0.52          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      ((((k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.52          = (k1_xboole_0)))
% 0.21/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf(t90_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.52         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X53 : $i, X54 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k7_relat_1 @ X53 @ X54))
% 0.21/0.52            = (k3_xboole_0 @ (k1_relat_1 @ X53) @ X54))
% 0.21/0.52          | ~ (v1_relat_1 @ X53))),
% 0.21/0.52      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X41 : $i, X42 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X53 : $i, X54 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k7_relat_1 @ X53 @ X54))
% 0.21/0.52            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X53) @ X54)))
% 0.21/0.52          | ~ (v1_relat_1 @ X53))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.52  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (k1_xboole_0)))
% 0.21/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf(t64_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.52         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X52 : $i]:
% 0.21/0.52         (((k1_relat_1 @ X52) != (k1_xboole_0))
% 0.21/0.52          | ((X52) = (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X52))),
% 0.21/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.21/0.52         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.21/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.21/0.52         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.21/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.21/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '31'])).
% 0.21/0.52  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.52         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.52         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.21/0.52             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.52       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.52       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('39', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['18', '37', '38'])).
% 0.21/0.52  thf('40', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['16', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X53 : $i, X54 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k7_relat_1 @ X53 @ X54))
% 0.21/0.52            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X53) @ X54)))
% 0.21/0.52          | ~ (v1_relat_1 @ X53))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X41 : $i, X42 : $i]:
% 0.21/0.52         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ X2)
% 0.21/0.52          | ((k1_setfam_1 @ (k2_tarski @ X0 @ X2)) != (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) != (k1_xboole_0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '45'])).
% 0.21/0.52  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.21/0.52         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf('50', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['18', '37'])).
% 0.21/0.52  thf('51', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('clc', [status(thm)], ['48', '51'])).
% 0.21/0.52  thf('53', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['14', '52'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
