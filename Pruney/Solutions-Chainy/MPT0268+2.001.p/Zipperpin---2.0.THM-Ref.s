%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8jVRJ1H23o

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:52 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 710 expanded)
%              Number of leaves         :   29 ( 228 expanded)
%              Depth                    :   21
%              Number of atoms          : 1122 (5242 expanded)
%              Number of equality atoms :  113 ( 640 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X28 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X54 ) @ X55 )
      | ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X30 @ X31 ) @ X31 )
        = X30 )
      | ~ ( r1_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X24 @ X26 ) @ ( k3_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( X16 != X17 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X17: $i] :
      ( r1_tarski @ X17 @ X17 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X19: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X21 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','42'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k5_xboole_0 @ X32 @ ( k5_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','42'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','42'])).

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k5_xboole_0 @ X32 @ ( k5_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','66'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('68',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('75',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('78',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ( ( k4_xboole_0 @ X19 @ X20 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','42'])).

thf('90',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('91',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k5_xboole_0 @ X32 @ ( k5_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['88','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X19: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X21 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['102','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','107'])).

thf('109',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('110',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('111',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','12','110'])).

thf('112',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['109','111'])).

thf('113',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','112'])).

thf('114',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['14','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8jVRJ1H23o
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.31/2.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.31/2.54  % Solved by: fo/fo7.sh
% 2.31/2.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.31/2.54  % done 2249 iterations in 2.089s
% 2.31/2.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.31/2.54  % SZS output start Refutation
% 2.31/2.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.31/2.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.31/2.54  thf(sk_B_type, type, sk_B: $i > $i).
% 2.31/2.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.31/2.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.31/2.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.31/2.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.31/2.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.31/2.54  thf(sk_A_type, type, sk_A: $i).
% 2.31/2.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.31/2.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.31/2.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.31/2.54  thf(t65_zfmisc_1, conjecture,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.31/2.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.31/2.54  thf(zf_stmt_0, negated_conjecture,
% 2.31/2.54    (~( ![A:$i,B:$i]:
% 2.31/2.54        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.31/2.54          ( ~( r2_hidden @ B @ A ) ) ) )),
% 2.31/2.54    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 2.31/2.54  thf('0', plain,
% 2.31/2.54      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 2.31/2.54        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 2.31/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.54  thf('1', plain,
% 2.31/2.54      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 2.31/2.54      inference('split', [status(esa)], ['0'])).
% 2.31/2.54  thf('2', plain,
% 2.31/2.54      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 2.31/2.54       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 2.31/2.54      inference('split', [status(esa)], ['0'])).
% 2.31/2.54  thf('3', plain,
% 2.31/2.54      (((r2_hidden @ sk_B_1 @ sk_A)
% 2.31/2.54        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 2.31/2.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.54  thf('4', plain,
% 2.31/2.54      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 2.31/2.54      inference('split', [status(esa)], ['3'])).
% 2.31/2.54  thf('5', plain,
% 2.31/2.54      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 2.31/2.54         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.31/2.54      inference('split', [status(esa)], ['0'])).
% 2.31/2.54  thf(t79_xboole_1, axiom,
% 2.31/2.54    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.31/2.54  thf('6', plain,
% 2.31/2.54      (![X28 : $i, X29 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X28 @ X29) @ X29)),
% 2.31/2.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.31/2.54  thf('7', plain,
% 2.31/2.54      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))
% 2.31/2.54         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.31/2.54      inference('sup+', [status(thm)], ['5', '6'])).
% 2.31/2.54  thf(symmetry_r1_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.31/2.54  thf('8', plain,
% 2.31/2.54      (![X9 : $i, X10 : $i]:
% 2.31/2.54         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 2.31/2.54      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.31/2.54  thf('9', plain,
% 2.31/2.54      (((r1_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))
% 2.31/2.54         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.31/2.54      inference('sup-', [status(thm)], ['7', '8'])).
% 2.31/2.54  thf(l24_zfmisc_1, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 2.31/2.54  thf('10', plain,
% 2.31/2.54      (![X52 : $i, X53 : $i]:
% 2.31/2.54         (~ (r1_xboole_0 @ (k1_tarski @ X52) @ X53) | ~ (r2_hidden @ X52 @ X53))),
% 2.31/2.54      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 2.31/2.54  thf('11', plain,
% 2.31/2.54      ((~ (r2_hidden @ sk_B_1 @ sk_A))
% 2.31/2.54         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.31/2.54      inference('sup-', [status(thm)], ['9', '10'])).
% 2.31/2.54  thf('12', plain,
% 2.31/2.54      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) | 
% 2.31/2.54       ~ ((r2_hidden @ sk_B_1 @ sk_A))),
% 2.31/2.54      inference('sup-', [status(thm)], ['4', '11'])).
% 2.31/2.54  thf('13', plain, (~ ((r2_hidden @ sk_B_1 @ sk_A))),
% 2.31/2.54      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 2.31/2.54  thf('14', plain, (~ (r2_hidden @ sk_B_1 @ sk_A)),
% 2.31/2.54      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 2.31/2.54  thf(l27_zfmisc_1, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.31/2.54  thf('15', plain,
% 2.31/2.54      (![X54 : $i, X55 : $i]:
% 2.31/2.54         ((r1_xboole_0 @ (k1_tarski @ X54) @ X55) | (r2_hidden @ X54 @ X55))),
% 2.31/2.54      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.31/2.54  thf(t88_xboole_1, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( r1_xboole_0 @ A @ B ) =>
% 2.31/2.54       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 2.31/2.54  thf('16', plain,
% 2.31/2.54      (![X30 : $i, X31 : $i]:
% 2.31/2.54         (((k4_xboole_0 @ (k2_xboole_0 @ X30 @ X31) @ X31) = (X30))
% 2.31/2.54          | ~ (r1_xboole_0 @ X30 @ X31))),
% 2.31/2.54      inference('cnf', [status(esa)], [t88_xboole_1])).
% 2.31/2.54  thf('17', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((r2_hidden @ X1 @ X0)
% 2.31/2.54          | ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X0)
% 2.31/2.54              = (k1_tarski @ X1)))),
% 2.31/2.54      inference('sup-', [status(thm)], ['15', '16'])).
% 2.31/2.54  thf(idempotence_k3_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 2.31/2.54  thf('18', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 2.31/2.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.31/2.54  thf(t112_xboole_1, axiom,
% 2.31/2.54    (![A:$i,B:$i,C:$i]:
% 2.31/2.54     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 2.31/2.54       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 2.31/2.54  thf('19', plain,
% 2.31/2.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 2.31/2.54           = (k3_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26))),
% 2.31/2.54      inference('cnf', [status(esa)], [t112_xboole_1])).
% 2.31/2.54  thf('20', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['18', '19'])).
% 2.31/2.54  thf(commutativity_k3_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.31/2.54  thf('21', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('22', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 2.31/2.54      inference('demod', [status(thm)], ['20', '21'])).
% 2.31/2.54  thf('23', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf(t100_xboole_1, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.31/2.54  thf('24', plain,
% 2.31/2.54      (![X22 : $i, X23 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X22 @ X23)
% 2.31/2.54           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.31/2.54  thf('25', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X0 @ X1)
% 2.31/2.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['23', '24'])).
% 2.31/2.54  thf('26', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X1 @ X0)
% 2.31/2.54           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['22', '25'])).
% 2.31/2.54  thf('27', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('28', plain,
% 2.31/2.54      (![X22 : $i, X23 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X22 @ X23)
% 2.31/2.54           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.31/2.54  thf('29', plain,
% 2.31/2.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k3_xboole_0 @ X24 @ X26) @ (k3_xboole_0 @ X25 @ X26))
% 2.31/2.54           = (k3_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26))),
% 2.31/2.54      inference('cnf', [status(esa)], [t112_xboole_1])).
% 2.31/2.54  thf('30', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 2.31/2.54           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['28', '29'])).
% 2.31/2.54  thf('31', plain,
% 2.31/2.54      (![X22 : $i, X23 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X22 @ X23)
% 2.31/2.54           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.31/2.54  thf('32', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('33', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 2.31/2.54           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.31/2.54  thf('34', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 2.31/2.54           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['27', '33'])).
% 2.31/2.54  thf('35', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 2.31/2.54           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['26', '34'])).
% 2.31/2.54  thf('36', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 2.31/2.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.31/2.54  thf('37', plain,
% 2.31/2.54      (![X22 : $i, X23 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X22 @ X23)
% 2.31/2.54           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.31/2.54  thf('38', plain,
% 2.31/2.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['36', '37'])).
% 2.31/2.54  thf(d10_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.31/2.54  thf('39', plain,
% 2.31/2.54      (![X16 : $i, X17 : $i]: ((r1_tarski @ X16 @ X17) | ((X16) != (X17)))),
% 2.31/2.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.31/2.54  thf('40', plain, (![X17 : $i]: (r1_tarski @ X17 @ X17)),
% 2.31/2.54      inference('simplify', [status(thm)], ['39'])).
% 2.31/2.54  thf(l32_xboole_1, axiom,
% 2.31/2.54    (![A:$i,B:$i]:
% 2.31/2.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.31/2.54  thf('41', plain,
% 2.31/2.54      (![X19 : $i, X21 : $i]:
% 2.31/2.54         (((k4_xboole_0 @ X19 @ X21) = (k1_xboole_0))
% 2.31/2.54          | ~ (r1_tarski @ X19 @ X21))),
% 2.31/2.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.31/2.54  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.31/2.54      inference('sup-', [status(thm)], ['40', '41'])).
% 2.31/2.54  thf('43', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 2.31/2.54      inference('demod', [status(thm)], ['38', '42'])).
% 2.31/2.54  thf(t91_xboole_1, axiom,
% 2.31/2.54    (![A:$i,B:$i,C:$i]:
% 2.31/2.54     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.31/2.54       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.31/2.54  thf('44', plain,
% 2.31/2.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ X34)
% 2.31/2.54           = (k5_xboole_0 @ X32 @ (k5_xboole_0 @ X33 @ X34)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.31/2.54  thf('45', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.31/2.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['43', '44'])).
% 2.31/2.54  thf('46', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 2.31/2.54      inference('demod', [status(thm)], ['38', '42'])).
% 2.31/2.54  thf('47', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.31/2.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['43', '44'])).
% 2.31/2.54  thf('48', plain,
% 2.31/2.54      (![X0 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['46', '47'])).
% 2.31/2.54  thf(t5_boole, axiom,
% 2.31/2.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.31/2.54  thf('49', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 2.31/2.54      inference('cnf', [status(esa)], [t5_boole])).
% 2.31/2.54  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.31/2.54      inference('demod', [status(thm)], ['48', '49'])).
% 2.31/2.54  thf('51', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('demod', [status(thm)], ['45', '50'])).
% 2.31/2.54  thf('52', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 2.31/2.54      inference('demod', [status(thm)], ['38', '42'])).
% 2.31/2.54  thf('53', plain,
% 2.31/2.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ X34)
% 2.31/2.54           = (k5_xboole_0 @ X32 @ (k5_xboole_0 @ X33 @ X34)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.31/2.54  thf('54', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k1_xboole_0)
% 2.31/2.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 2.31/2.54      inference('sup+', [status(thm)], ['52', '53'])).
% 2.31/2.54  thf('55', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('demod', [status(thm)], ['45', '50'])).
% 2.31/2.54  thf('56', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['54', '55'])).
% 2.31/2.54  thf('57', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 2.31/2.54      inference('cnf', [status(esa)], [t5_boole])).
% 2.31/2.54  thf('58', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 2.31/2.54      inference('demod', [status(thm)], ['56', '57'])).
% 2.31/2.54  thf('59', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('demod', [status(thm)], ['45', '50'])).
% 2.31/2.54  thf('60', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X1 @ X0)
% 2.31/2.54           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['22', '25'])).
% 2.31/2.54  thf('61', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (k3_xboole_0 @ X1 @ X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['59', '60'])).
% 2.31/2.54  thf('62', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X1 @ X0)
% 2.31/2.54           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['58', '61'])).
% 2.31/2.54  thf('63', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1)
% 2.31/2.54           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['51', '62'])).
% 2.31/2.54  thf('64', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf('65', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X1 @ X0)
% 2.31/2.54           = (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['58', '61'])).
% 2.31/2.54  thf('66', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X1)
% 2.31/2.54           = (k4_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.31/2.54  thf('67', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 2.31/2.54           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.31/2.54      inference('demod', [status(thm)], ['35', '66'])).
% 2.31/2.54  thf(t7_xboole_0, axiom,
% 2.31/2.54    (![A:$i]:
% 2.31/2.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.31/2.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.31/2.54  thf('68', plain,
% 2.31/2.54      (![X15 : $i]:
% 2.31/2.54         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 2.31/2.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.31/2.54  thf('69', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.31/2.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.31/2.54  thf(d4_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i,C:$i]:
% 2.31/2.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.31/2.54       ( ![D:$i]:
% 2.31/2.54         ( ( r2_hidden @ D @ C ) <=>
% 2.31/2.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.31/2.54  thf('70', plain,
% 2.31/2.54      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.31/2.54         (~ (r2_hidden @ X6 @ X5)
% 2.31/2.54          | (r2_hidden @ X6 @ X4)
% 2.31/2.54          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 2.31/2.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.31/2.54  thf('71', plain,
% 2.31/2.54      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.31/2.54         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.31/2.54      inference('simplify', [status(thm)], ['70'])).
% 2.31/2.54  thf('72', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.54         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.31/2.54      inference('sup-', [status(thm)], ['69', '71'])).
% 2.31/2.54  thf('73', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.31/2.54          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 2.31/2.54      inference('sup-', [status(thm)], ['68', '72'])).
% 2.31/2.54  thf('74', plain,
% 2.31/2.54      (![X15 : $i]:
% 2.31/2.54         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 2.31/2.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.31/2.54  thf('75', plain,
% 2.31/2.54      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.31/2.54         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.31/2.54      inference('simplify', [status(thm)], ['70'])).
% 2.31/2.54  thf('76', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.31/2.54          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 2.31/2.54      inference('sup-', [status(thm)], ['74', '75'])).
% 2.31/2.54  thf('77', plain,
% 2.31/2.54      (![X22 : $i, X23 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X22 @ X23)
% 2.31/2.54           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.31/2.54  thf(t1_xboole_0, axiom,
% 2.31/2.54    (![A:$i,B:$i,C:$i]:
% 2.31/2.54     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 2.31/2.54       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 2.31/2.54  thf('78', plain,
% 2.31/2.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.31/2.54         (~ (r2_hidden @ X11 @ X12)
% 2.31/2.54          | ~ (r2_hidden @ X11 @ X13)
% 2.31/2.54          | ~ (r2_hidden @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.31/2.54  thf('79', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.54         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 2.31/2.54          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54          | ~ (r2_hidden @ X2 @ X1))),
% 2.31/2.54      inference('sup-', [status(thm)], ['77', '78'])).
% 2.31/2.54  thf('80', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.54         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.31/2.54      inference('sup-', [status(thm)], ['69', '71'])).
% 2.31/2.54  thf('81', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.54         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('clc', [status(thm)], ['79', '80'])).
% 2.31/2.54  thf('82', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) = (k1_xboole_0))
% 2.31/2.54          | ~ (r2_hidden @ 
% 2.31/2.54               (sk_B @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) @ 
% 2.31/2.54               (k4_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('sup-', [status(thm)], ['76', '81'])).
% 2.31/2.54  thf('83', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54            = (k1_xboole_0))
% 2.31/2.54          | ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54              = (k1_xboole_0)))),
% 2.31/2.54      inference('sup-', [status(thm)], ['73', '82'])).
% 2.31/2.54  thf('84', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (k1_xboole_0))),
% 2.31/2.54      inference('simplify', [status(thm)], ['83'])).
% 2.31/2.54  thf('85', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (k3_xboole_0 @ X1 @ X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['59', '60'])).
% 2.31/2.54  thf('86', plain,
% 2.31/2.54      (![X19 : $i, X20 : $i]:
% 2.31/2.54         ((r1_tarski @ X19 @ X20)
% 2.31/2.54          | ((k4_xboole_0 @ X19 @ X20) != (k1_xboole_0)))),
% 2.31/2.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.31/2.54  thf('87', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 2.31/2.54          | (r1_tarski @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('sup-', [status(thm)], ['85', '86'])).
% 2.31/2.54  thf('88', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k1_xboole_0) != (k1_xboole_0))
% 2.31/2.54          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 2.31/2.54             (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 2.31/2.54      inference('sup-', [status(thm)], ['84', '87'])).
% 2.31/2.54  thf('89', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 2.31/2.54      inference('demod', [status(thm)], ['38', '42'])).
% 2.31/2.54  thf('90', plain,
% 2.31/2.54      (![X22 : $i, X23 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X22 @ X23)
% 2.31/2.54           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.31/2.54  thf('91', plain,
% 2.31/2.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ X34)
% 2.31/2.54           = (k5_xboole_0 @ X32 @ (k5_xboole_0 @ X33 @ X34)))),
% 2.31/2.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.31/2.54  thf('92', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 2.31/2.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 2.31/2.54      inference('sup+', [status(thm)], ['90', '91'])).
% 2.31/2.54  thf('93', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['89', '92'])).
% 2.31/2.54  thf('94', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 2.31/2.54      inference('cnf', [status(esa)], [t5_boole])).
% 2.31/2.54  thf('95', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (X1))),
% 2.31/2.54      inference('demod', [status(thm)], ['93', '94'])).
% 2.31/2.54  thf('96', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k1_xboole_0) != (k1_xboole_0))
% 2.31/2.54          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 2.31/2.54      inference('demod', [status(thm)], ['88', '95'])).
% 2.31/2.54  thf('97', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 2.31/2.54      inference('simplify', [status(thm)], ['96'])).
% 2.31/2.54  thf('98', plain,
% 2.31/2.54      (![X19 : $i, X21 : $i]:
% 2.31/2.54         (((k4_xboole_0 @ X19 @ X21) = (k1_xboole_0))
% 2.31/2.54          | ~ (r1_tarski @ X19 @ X21))),
% 2.31/2.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 2.31/2.54  thf('99', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 2.31/2.54      inference('sup-', [status(thm)], ['97', '98'])).
% 2.31/2.54  thf('100', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.31/2.54      inference('demod', [status(thm)], ['67', '99'])).
% 2.31/2.54  thf('101', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.31/2.54           = (X1))),
% 2.31/2.54      inference('demod', [status(thm)], ['93', '94'])).
% 2.31/2.54  thf('102', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 2.31/2.54           k1_xboole_0) = (X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['100', '101'])).
% 2.31/2.54  thf('103', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 2.31/2.54      inference('demod', [status(thm)], ['56', '57'])).
% 2.31/2.54  thf('104', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.31/2.54      inference('demod', [status(thm)], ['45', '50'])).
% 2.31/2.54  thf('105', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 2.31/2.54      inference('sup+', [status(thm)], ['103', '104'])).
% 2.31/2.54  thf('106', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.31/2.54      inference('demod', [status(thm)], ['48', '49'])).
% 2.31/2.54  thf('107', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 2.31/2.54      inference('demod', [status(thm)], ['102', '105', '106'])).
% 2.31/2.54  thf('108', plain,
% 2.31/2.54      (![X0 : $i, X1 : $i]:
% 2.31/2.54         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 2.31/2.54          | (r2_hidden @ X0 @ X1))),
% 2.31/2.54      inference('sup+', [status(thm)], ['17', '107'])).
% 2.31/2.54  thf('109', plain,
% 2.31/2.54      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 2.31/2.54         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 2.31/2.54      inference('split', [status(esa)], ['3'])).
% 2.31/2.54  thf('110', plain,
% 2.31/2.54      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) | 
% 2.31/2.54       ((r2_hidden @ sk_B_1 @ sk_A))),
% 2.31/2.54      inference('split', [status(esa)], ['3'])).
% 2.31/2.54  thf('111', plain,
% 2.31/2.54      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 2.31/2.54      inference('sat_resolution*', [status(thm)], ['2', '12', '110'])).
% 2.31/2.54  thf('112', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A))),
% 2.31/2.54      inference('simpl_trail', [status(thm)], ['109', '111'])).
% 2.31/2.54  thf('113', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A))),
% 2.31/2.54      inference('sup-', [status(thm)], ['108', '112'])).
% 2.31/2.54  thf('114', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 2.31/2.54      inference('simplify', [status(thm)], ['113'])).
% 2.31/2.54  thf('115', plain, ($false), inference('demod', [status(thm)], ['14', '114'])).
% 2.31/2.54  
% 2.31/2.54  % SZS output end Refutation
% 2.31/2.54  
% 2.31/2.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
