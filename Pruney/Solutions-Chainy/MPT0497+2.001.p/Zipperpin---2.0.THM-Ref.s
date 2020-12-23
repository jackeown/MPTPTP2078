%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9bUq7kRW7U

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 114 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  619 ( 935 expanded)
%              Number of equality atoms :   76 ( 108 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X37 ) @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k4_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('12',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) @ ( k4_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      = ( k1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,
    ( ( ( ( k1_relat_1 @ sk_B )
       != ( k1_relat_1 @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('37',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X3 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X37 ) @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X36: $i] :
      ( ( ( k1_relat_1 @ X36 )
       != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','23','24','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9bUq7kRW7U
% 0.13/0.36  % Computer   : n003.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:30:42 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 119 iterations in 0.040s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(t95_relat_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.50         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( v1_relat_1 @ B ) =>
% 0.22/0.50          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.50            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.50        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.50       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.22/0.50        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf(t90_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.22/0.50         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X37 : $i, X38 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.22/0.50            = (k3_xboole_0 @ (k1_relat_1 @ X37) @ X38))
% 0.22/0.50          | ~ (v1_relat_1 @ X37))),
% 0.22/0.50      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.50  thf(t12_setfam_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X32 : $i, X33 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X37 : $i, X38 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.22/0.50            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X37) @ X38)))
% 0.22/0.50          | ~ (v1_relat_1 @ X37))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (((((k1_relat_1 @ k1_xboole_0)
% 0.22/0.50           = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.22/0.50         | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['3', '6'])).
% 0.22/0.50  thf(t60_relat_1, axiom,
% 0.22/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      ((((k1_xboole_0)
% 0.22/0.50          = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.22/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.50  thf(t51_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.50       ( A ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k4_xboole_0 @ X7 @ X8))
% 0.22/0.50           = (X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X32 : $i, X33 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8)) @ 
% 0.22/0.50           (k4_xboole_0 @ X7 @ X8)) = (X7))),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((((k2_xboole_0 @ k1_xboole_0 @ 
% 0.22/0.50          (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) = (k1_relat_1 @ sk_B)))
% 0.22/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['10', '13'])).
% 0.22/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.50  thf(t1_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('16', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.50  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B)))
% 0.22/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['14', '17'])).
% 0.22/0.50  thf(t83_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X9 : $i, X11 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.22/0.50         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.22/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.50         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.50         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.50       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.50       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf(dt_k7_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X34 : $i, X35 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X34) | (v1_relat_1 @ (k7_relat_1 @ X34 @ X35)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B)))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf(t48_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.22/0.50           = (k3_xboole_0 @ X5 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X32 : $i, X33 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.22/0.50           = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))),
% 0.22/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.22/0.50          = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['28', '31'])).
% 0.22/0.50  thf(t3_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('33', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.22/0.50           = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))),
% 0.22/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X0 @ X0)
% 0.22/0.50           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf(t2_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X32 : $i, X33 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X3 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X3 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      ((((k1_xboole_0)
% 0.22/0.50          = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['32', '39'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X37 : $i, X38 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (k7_relat_1 @ X37 @ X38))
% 0.22/0.50            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X37) @ X38)))
% 0.22/0.50          | ~ (v1_relat_1 @ X37))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf(t64_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X36 : $i]:
% 0.22/0.50         (((k1_relat_1 @ X36) != (k1_xboole_0))
% 0.22/0.50          | ((X36) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X36))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X1) @ X0))
% 0.22/0.50            != (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X1)
% 0.22/0.50          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.50          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.50         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.22/0.50         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.22/0.50         | ~ (v1_relat_1 @ sk_B)))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['40', '43'])).
% 0.22/0.50  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.50         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.22/0.50         | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.22/0.50         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '47'])).
% 0.22/0.50  thf('49', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.22/0.50         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.22/0.50         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.22/0.50         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.22/0.50             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.50  thf('53', plain,
% 0.22/0.50      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.22/0.50       (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['52'])).
% 0.22/0.50  thf('54', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['1', '23', '24', '53'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
