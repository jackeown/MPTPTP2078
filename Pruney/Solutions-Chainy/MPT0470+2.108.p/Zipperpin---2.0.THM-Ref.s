%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YEpmTPQDtH

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:42 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 155 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  628 (1011 expanded)
%              Number of equality atoms :   50 (  90 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X32 @ X31 ) ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ X24 )
      | ( r2_hidden @ ( sk_B @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( r1_xboole_0 @ X10 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('28',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('36',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X34 @ X33 ) )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ ( k1_relat_1 @ X33 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('41',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','9'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('53',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('64',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['34','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['66','67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YEpmTPQDtH
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:44:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 318 iterations in 0.186s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.65  thf(dt_k5_relat_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.47/0.65       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      (![X27 : $i, X28 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X27)
% 0.47/0.65          | ~ (v1_relat_1 @ X28)
% 0.47/0.65          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.65  thf(t60_relat_1, axiom,
% 0.47/0.65    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.65     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.65  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.65  thf(t45_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( v1_relat_1 @ B ) =>
% 0.47/0.65           ( r1_tarski @
% 0.47/0.65             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X31 : $i, X32 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X31)
% 0.47/0.65          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X32 @ X31)) @ 
% 0.47/0.65             (k2_relat_1 @ X31))
% 0.47/0.65          | ~ (v1_relat_1 @ X32))),
% 0.47/0.65      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.65           k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.65  thf(d1_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) <=>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ~( ( r2_hidden @ B @ A ) & 
% 0.47/0.65              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X24 : $i]: ((v1_relat_1 @ X24) | (r2_hidden @ (sk_B @ X24) @ X24))),
% 0.47/0.65      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.47/0.65  thf(t2_boole, axiom,
% 0.47/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.65  thf(t4_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.47/0.65          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.65  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.47/0.65  thf('8', plain, (![X10 : $i]: (r1_xboole_0 @ X10 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.47/0.65  thf('9', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.47/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.65  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '9'])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.65           k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['3', '10'])).
% 0.47/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.65  thf('12', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.47/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.65  thf(d10_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X5 : $i, X7 : $i]:
% 0.47/0.65         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '14'])).
% 0.47/0.65  thf(fc9_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.47/0.65       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X30 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ (k2_relat_1 @ X30))
% 0.47/0.65          | ~ (v1_relat_1 @ X30)
% 0.47/0.65          | (v1_xboole_0 @ X30))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.65  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['17', '18'])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['0', '19'])).
% 0.47/0.65  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '9'])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.47/0.65  thf(l13_xboole_0, axiom,
% 0.47/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.65  thf(t62_relat_1, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.47/0.65         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( v1_relat_1 @ A ) =>
% 0.47/0.65          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.47/0.65            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.47/0.65        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('split', [status(esa)], ['28'])).
% 0.47/0.65  thf('30', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['27', '29'])).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      ((![X0 : $i, X1 : $i]:
% 0.47/0.65          (((X0) != (k1_xboole_0))
% 0.47/0.65           | ~ (v1_xboole_0 @ X0)
% 0.47/0.65           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.47/0.65           | ~ (v1_xboole_0 @ X1)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['26', '30'])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      ((![X1 : $i]:
% 0.47/0.65          (~ (v1_xboole_0 @ X1)
% 0.47/0.65           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.47/0.65           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('simplify', [status(thm)], ['31'])).
% 0.47/0.65  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('34', plain,
% 0.47/0.65      ((![X1 : $i]:
% 0.47/0.65          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('simplify_reflect+', [status(thm)], ['32', '33'])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (![X27 : $i, X28 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X27)
% 0.47/0.65          | ~ (v1_relat_1 @ X28)
% 0.47/0.65          | (v1_relat_1 @ (k5_relat_1 @ X27 @ X28)))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.65  thf('36', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.65  thf(t46_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( v1_relat_1 @ B ) =>
% 0.47/0.65           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.65             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.65  thf('37', plain,
% 0.47/0.65      (![X33 : $i, X34 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X33)
% 0.47/0.65          | ((k1_relat_1 @ (k5_relat_1 @ X34 @ X33)) = (k1_relat_1 @ X34))
% 0.47/0.65          | ~ (r1_tarski @ (k2_relat_1 @ X34) @ (k1_relat_1 @ X33))
% 0.47/0.65          | ~ (v1_relat_1 @ X34))),
% 0.47/0.65      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.65          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65              = (k1_relat_1 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.47/0.65  thf('39', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.47/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.65  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '9'])).
% 0.47/0.65  thf('41', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.47/0.65  thf(fc8_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.47/0.65       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      (![X29 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ (k1_relat_1 @ X29))
% 0.47/0.65          | ~ (v1_relat_1 @ X29)
% 0.47/0.65          | (v1_xboole_0 @ X29))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.47/0.65  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['44', '45'])).
% 0.47/0.65  thf('47', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['35', '46'])).
% 0.47/0.65  thf('48', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '9'])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['47', '48'])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.47/0.65  thf('51', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['24', '25'])).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.65  thf('53', plain,
% 0.47/0.65      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('split', [status(esa)], ['28'])).
% 0.47/0.65  thf('54', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.65  thf('55', plain,
% 0.47/0.65      ((![X0 : $i, X1 : $i]:
% 0.47/0.65          (((X0) != (k1_xboole_0))
% 0.47/0.65           | ~ (v1_xboole_0 @ X0)
% 0.47/0.65           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.47/0.65           | ~ (v1_xboole_0 @ X1)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['51', '54'])).
% 0.47/0.65  thf('56', plain,
% 0.47/0.65      ((![X1 : $i]:
% 0.47/0.65          (~ (v1_xboole_0 @ X1)
% 0.47/0.65           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.47/0.65           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('simplify', [status(thm)], ['55'])).
% 0.47/0.65  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      ((![X1 : $i]:
% 0.47/0.65          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('simplify_reflect+', [status(thm)], ['56', '57'])).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['50', '58'])).
% 0.47/0.65  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('62', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.47/0.65  thf('63', plain,
% 0.47/0.65      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.47/0.65       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.65      inference('split', [status(esa)], ['28'])).
% 0.47/0.65  thf('64', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['62', '63'])).
% 0.47/0.65  thf('65', plain,
% 0.47/0.65      (![X1 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1)))),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['34', '64'])).
% 0.47/0.65  thf('66', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['23', '65'])).
% 0.47/0.65  thf('67', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('69', plain, ($false),
% 0.47/0.65      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
