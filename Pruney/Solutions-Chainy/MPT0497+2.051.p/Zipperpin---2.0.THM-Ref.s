%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8s6e1Dy0Sv

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:13 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 192 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :   18
%              Number of atoms          :  758 (1646 expanded)
%              Number of equality atoms :   71 ( 167 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t82_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t82_xboole_1])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X7 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','30'])).

thf('32',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf('43',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('45',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('46',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('50',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','30','49'])).

thf('51',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k4_xboole_0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_xboole_0 @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k3_xboole_0 @ ( k1_relat_1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_xboole_0 @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_tarski @ X3 @ ( k3_xboole_0 @ ( k1_relat_1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','65'])).

thf('67',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['32','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8s6e1Dy0Sv
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:45:37 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 574 iterations in 0.243s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(t95_relat_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ B ) =>
% 0.46/0.68       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.68         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i]:
% 0.46/0.68        ( ( v1_relat_1 @ B ) =>
% 0.46/0.68          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.68            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.46/0.68        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.46/0.68         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.46/0.68       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('split', [status(esa)], ['0'])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.46/0.68        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.46/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.68      inference('split', [status(esa)], ['3'])).
% 0.46/0.68  thf(t83_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i]:
% 0.46/0.68         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.46/0.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B)))
% 0.46/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.68  thf(t48_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X4 : $i, X5 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.46/0.68           = (k3_xboole_0 @ X4 @ X5))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.46/0.68          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.46/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf(t3_boole, axiom,
% 0.46/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.68  thf('9', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X4 : $i, X5 : $i]:
% 0.46/0.68         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.46/0.68           = (k3_xboole_0 @ X4 @ X5))),
% 0.46/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.68      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      ((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0)
% 0.46/0.68          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.46/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['8', '11'])).
% 0.46/0.68  thf(dt_k7_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (![X20 : $i, X21 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.68  thf(t90_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ B ) =>
% 0.46/0.68       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.46/0.68         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X25 : $i, X26 : $i]:
% 0.46/0.68         (((k1_relat_1 @ (k7_relat_1 @ X25 @ X26))
% 0.46/0.68            = (k3_xboole_0 @ (k1_relat_1 @ X25) @ X26))
% 0.46/0.68          | ~ (v1_relat_1 @ X25))),
% 0.46/0.68      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.46/0.68  thf(t64_relat_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ A ) =>
% 0.46/0.68       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.68           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.68         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X22 : $i]:
% 0.46/0.68         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.46/0.68          | ((X22) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X22))),
% 0.46/0.68      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X1)
% 0.46/0.68          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.46/0.68          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v1_relat_1 @ X1)
% 0.46/0.68          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X1)
% 0.46/0.68          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['13', '16'])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.46/0.68          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.46/0.68          | ~ (v1_relat_1 @ X1))),
% 0.46/0.68      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (((((k3_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0) != (k1_xboole_0))
% 0.46/0.68         | ~ (v1_relat_1 @ sk_B)
% 0.46/0.68         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.46/0.68         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['12', '18'])).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.69  thf(t82_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X8 : $i, X9 : $i]:
% 0.46/0.69         (r1_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8))),
% 0.46/0.69      inference('cnf', [status(esa)], [t82_xboole_1])).
% 0.46/0.69  thf(t66_xboole_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.46/0.69       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X7 @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.46/0.69  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['20', '23'])).
% 0.46/0.69  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('26', plain,
% 0.46/0.69      (((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.69         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.46/0.69         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.46/0.69         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['26'])).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.46/0.69         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.46/0.69      inference('split', [status(esa)], ['0'])).
% 0.46/0.69  thf('29', plain,
% 0.46/0.69      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.69         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.46/0.69             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.69  thf('30', plain,
% 0.46/0.69      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.46/0.69       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.69      inference('simplify', [status(thm)], ['29'])).
% 0.46/0.69  thf('31', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.69      inference('sat_resolution*', [status(thm)], ['2', '30'])).
% 0.46/0.69  thf('32', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.46/0.69  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf('34', plain,
% 0.46/0.69      (![X4 : $i, X5 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.46/0.69           = (k3_xboole_0 @ X4 @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.69  thf('36', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.69  thf('37', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.46/0.69      inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i]:
% 0.46/0.69         (((k1_relat_1 @ (k7_relat_1 @ X25 @ X26))
% 0.46/0.69            = (k3_xboole_0 @ (k1_relat_1 @ X25) @ X26))
% 0.46/0.69          | ~ (v1_relat_1 @ X25))),
% 0.46/0.69      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.46/0.69  thf(t87_relat_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( v1_relat_1 @ B ) =>
% 0.46/0.69       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.46/0.69  thf('39', plain,
% 0.46/0.69      (![X23 : $i, X24 : $i]:
% 0.46/0.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X23 @ X24)) @ X24)
% 0.46/0.69          | ~ (v1_relat_1 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.46/0.69  thf('40', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0)
% 0.46/0.69          | ~ (v1_relat_1 @ X1)
% 0.46/0.69          | ~ (v1_relat_1 @ X1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['38', '39'])).
% 0.46/0.69  thf('41', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (~ (v1_relat_1 @ X1)
% 0.46/0.69          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0))),
% 0.46/0.69      inference('simplify', [status(thm)], ['40'])).
% 0.46/0.69  thf('42', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.46/0.69          | ~ (v1_relat_1 @ X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['37', '41'])).
% 0.46/0.69  thf('43', plain,
% 0.46/0.69      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.46/0.69         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.46/0.69      inference('split', [status(esa)], ['3'])).
% 0.46/0.69  thf('44', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i]:
% 0.46/0.69         (((k1_relat_1 @ (k7_relat_1 @ X25 @ X26))
% 0.46/0.69            = (k3_xboole_0 @ (k1_relat_1 @ X25) @ X26))
% 0.46/0.69          | ~ (v1_relat_1 @ X25))),
% 0.46/0.69      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.46/0.69  thf('45', plain,
% 0.46/0.69      (((((k1_relat_1 @ k1_xboole_0)
% 0.46/0.69           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.46/0.69         | ~ (v1_relat_1 @ sk_B)))
% 0.46/0.69         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.46/0.69      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.69  thf(t60_relat_1, axiom,
% 0.46/0.69    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.69     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.69  thf('46', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.69      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.69  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('48', plain,
% 0.46/0.69      ((((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.46/0.69         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.46/0.69      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.46/0.69  thf('49', plain,
% 0.46/0.69      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.46/0.69       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.69      inference('split', [status(esa)], ['3'])).
% 0.46/0.69  thf('50', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.46/0.69      inference('sat_resolution*', [status(thm)], ['2', '30', '49'])).
% 0.46/0.69  thf('51', plain,
% 0.46/0.69      (((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['48', '50'])).
% 0.46/0.69  thf('52', plain,
% 0.46/0.69      (![X4 : $i, X5 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.46/0.69           = (k3_xboole_0 @ X4 @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.69  thf('53', plain,
% 0.46/0.69      (![X4 : $i, X5 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.46/0.69           = (k3_xboole_0 @ X4 @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.69  thf('54', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.69           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.69  thf('55', plain,
% 0.46/0.69      (![X25 : $i, X26 : $i]:
% 0.46/0.69         (((k1_relat_1 @ (k7_relat_1 @ X25 @ X26))
% 0.46/0.69            = (k3_xboole_0 @ (k1_relat_1 @ X25) @ X26))
% 0.46/0.69          | ~ (v1_relat_1 @ X25))),
% 0.46/0.69      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.46/0.69  thf('56', plain,
% 0.46/0.69      (![X23 : $i, X24 : $i]:
% 0.46/0.69         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X23 @ X24)) @ X24)
% 0.46/0.69          | ~ (v1_relat_1 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.46/0.69  thf(t106_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.46/0.69       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.46/0.69  thf('57', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         ((r1_xboole_0 @ X0 @ X2)
% 0.46/0.69          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.46/0.69  thf('58', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (v1_relat_1 @ X2)
% 0.46/0.69          | (r1_xboole_0 @ 
% 0.46/0.69             (k1_relat_1 @ (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.69  thf('59', plain,
% 0.46/0.69      (![X10 : $i, X11 : $i]:
% 0.46/0.69         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.69  thf('60', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (v1_relat_1 @ X2)
% 0.46/0.69          | ((k4_xboole_0 @ 
% 0.46/0.69              (k1_relat_1 @ (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))) @ X0)
% 0.46/0.69              = (k1_relat_1 @ (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.69  thf('61', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         ((r1_xboole_0 @ X0 @ X2)
% 0.46/0.69          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.53/0.69      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.53/0.69  thf('62', plain,
% 0.53/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.69         (~ (r1_tarski @ X3 @ 
% 0.53/0.69             (k1_relat_1 @ (k7_relat_1 @ X2 @ (k4_xboole_0 @ X1 @ X0))))
% 0.53/0.69          | ~ (v1_relat_1 @ X2)
% 0.53/0.69          | (r1_xboole_0 @ X3 @ X0))),
% 0.53/0.69      inference('sup-', [status(thm)], ['60', '61'])).
% 0.53/0.69  thf('63', plain,
% 0.53/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.69         (~ (r1_tarski @ X3 @ 
% 0.53/0.69             (k3_xboole_0 @ (k1_relat_1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))
% 0.53/0.69          | ~ (v1_relat_1 @ X2)
% 0.53/0.69          | (r1_xboole_0 @ X3 @ X0)
% 0.53/0.69          | ~ (v1_relat_1 @ X2))),
% 0.53/0.69      inference('sup-', [status(thm)], ['55', '62'])).
% 0.53/0.69  thf('64', plain,
% 0.53/0.69      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.69         ((r1_xboole_0 @ X3 @ X0)
% 0.53/0.69          | ~ (v1_relat_1 @ X2)
% 0.53/0.69          | ~ (r1_tarski @ X3 @ 
% 0.53/0.69               (k3_xboole_0 @ (k1_relat_1 @ X2) @ (k4_xboole_0 @ X1 @ X0))))),
% 0.53/0.69      inference('simplify', [status(thm)], ['63'])).
% 0.53/0.69  thf('65', plain,
% 0.53/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.69         (~ (r1_tarski @ X2 @ 
% 0.53/0.69             (k4_xboole_0 @ (k1_relat_1 @ X1) @ 
% 0.53/0.69              (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.53/0.69          | ~ (v1_relat_1 @ X1)
% 0.53/0.69          | (r1_xboole_0 @ X2 @ X0))),
% 0.53/0.69      inference('sup-', [status(thm)], ['54', '64'])).
% 0.53/0.69  thf('66', plain,
% 0.53/0.69      (![X0 : $i]:
% 0.53/0.69         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0))
% 0.53/0.69          | (r1_xboole_0 @ X0 @ sk_A)
% 0.53/0.69          | ~ (v1_relat_1 @ sk_B))),
% 0.53/0.69      inference('sup-', [status(thm)], ['51', '65'])).
% 0.53/0.69  thf('67', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.53/0.69      inference('cnf', [status(esa)], [t3_boole])).
% 0.53/0.69  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.69  thf('69', plain,
% 0.53/0.69      (![X0 : $i]:
% 0.53/0.69         (~ (r1_tarski @ X0 @ (k1_relat_1 @ sk_B)) | (r1_xboole_0 @ X0 @ sk_A))),
% 0.53/0.69      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.53/0.69  thf('70', plain,
% 0.53/0.69      ((~ (v1_relat_1 @ sk_B) | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.53/0.69      inference('sup-', [status(thm)], ['42', '69'])).
% 0.53/0.69  thf('71', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.69  thf('72', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.53/0.69      inference('demod', [status(thm)], ['70', '71'])).
% 0.53/0.69  thf('73', plain, ($false), inference('demod', [status(thm)], ['32', '72'])).
% 0.53/0.69  
% 0.53/0.69  % SZS output end Refutation
% 0.53/0.69  
% 0.53/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
