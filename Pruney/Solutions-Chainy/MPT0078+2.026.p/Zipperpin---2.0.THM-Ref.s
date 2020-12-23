%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yQ7csUGcy3

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:56 EST 2020

% Result     : Theorem 8.17s
% Output     : Refutation 8.17s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 788 expanded)
%              Number of leaves         :   27 ( 273 expanded)
%              Depth                    :   15
%              Number of atoms          :  957 (5880 expanded)
%              Number of equality atoms :   86 ( 555 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r1_tarski @ X33 @ ( k2_xboole_0 @ X34 @ X35 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k2_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X36 ) ) )
      | ~ ( r1_tarski @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k2_xboole_0 @ X36 @ X37 ) )
      | ~ ( r1_tarski @ X36 @ X37 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ X0 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X39 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X32: $i] :
      ( ( k4_xboole_0 @ X32 @ k1_xboole_0 )
      = X32 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X27: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X29 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X24 ) ) @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k2_xboole_0 @ X36 @ X37 ) )
      | ~ ( r1_tarski @ X36 @ X37 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k2_xboole_0 @ X36 @ X37 ) )
      | ~ ( r1_tarski @ X36 @ X37 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X38: $i] :
      ( ( r1_xboole_0 @ X38 @ X38 )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('52',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X21: $i] :
      ( ( k3_xboole_0 @ X21 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('55',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X39 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','64'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','67'])).

thf('69',plain,
    ( sk_C_2
    = ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','19','28','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','62','63'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','67'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','62','63'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ X0 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ sk_C_2 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','67'])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('87',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r1_tarski @ X33 @ ( k2_xboole_0 @ X34 @ X35 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X33 @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X25 @ X26 ) @ X25 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    r1_tarski @ sk_A @ sk_C_2 ),
    inference('sup+',[status(thm)],['85','92'])).

thf('94',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k2_xboole_0 @ X36 @ X37 ) )
      | ~ ( r1_tarski @ X36 @ X37 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('95',plain,
    ( sk_C_2
    = ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','67'])).

thf('97',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X39 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('101',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('103',plain,(
    sk_C_2 = sk_A ),
    inference(demod,[status(thm)],['69','78','95','96','101','102'])).

thf('104',plain,(
    sk_A != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yQ7csUGcy3
% 0.12/0.37  % Computer   : n012.cluster.edu
% 0.12/0.37  % Model      : x86_64 x86_64
% 0.12/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.37  % Memory     : 8042.1875MB
% 0.12/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.37  % CPULimit   : 60
% 0.12/0.37  % DateTime   : Tue Dec  1 10:55:22 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 8.17/8.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.17/8.41  % Solved by: fo/fo7.sh
% 8.17/8.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.17/8.41  % done 7718 iterations in 7.928s
% 8.17/8.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.17/8.41  % SZS output start Refutation
% 8.17/8.41  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.17/8.41  thf(sk_B_type, type, sk_B: $i).
% 8.17/8.41  thf(sk_C_2_type, type, sk_C_2: $i).
% 8.17/8.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.17/8.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.17/8.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.17/8.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.17/8.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.17/8.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.17/8.41  thf(sk_A_type, type, sk_A: $i).
% 8.17/8.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.17/8.41  thf(t36_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.17/8.41  thf('0', plain,
% 8.17/8.41      (![X25 : $i, X26 : $i]: (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X25)),
% 8.17/8.41      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.17/8.41  thf(t44_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i,C:$i]:
% 8.17/8.41     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 8.17/8.41       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 8.17/8.41  thf('1', plain,
% 8.17/8.41      (![X33 : $i, X34 : $i, X35 : $i]:
% 8.17/8.41         ((r1_tarski @ X33 @ (k2_xboole_0 @ X34 @ X35))
% 8.17/8.41          | ~ (r1_tarski @ (k4_xboole_0 @ X33 @ X34) @ X35))),
% 8.17/8.41      inference('cnf', [status(esa)], [t44_xboole_1])).
% 8.17/8.41  thf('2', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['0', '1'])).
% 8.17/8.41  thf(t45_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i]:
% 8.17/8.41     ( ( r1_tarski @ A @ B ) =>
% 8.17/8.41       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 8.17/8.41  thf('3', plain,
% 8.17/8.41      (![X36 : $i, X37 : $i]:
% 8.17/8.41         (((X37) = (k2_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X36)))
% 8.17/8.41          | ~ (r1_tarski @ X36 @ X37))),
% 8.17/8.41      inference('cnf', [status(esa)], [t45_xboole_1])).
% 8.17/8.41  thf(t39_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i]:
% 8.17/8.41     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.17/8.41  thf('4', plain,
% 8.17/8.41      (![X30 : $i, X31 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30))
% 8.17/8.41           = (k2_xboole_0 @ X30 @ X31))),
% 8.17/8.41      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.17/8.41  thf('5', plain,
% 8.17/8.41      (![X36 : $i, X37 : $i]:
% 8.17/8.41         (((X37) = (k2_xboole_0 @ X36 @ X37)) | ~ (r1_tarski @ X36 @ X37))),
% 8.17/8.41      inference('demod', [status(thm)], ['3', '4'])).
% 8.17/8.41  thf('6', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X1 @ X0)
% 8.17/8.41           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.17/8.41      inference('sup-', [status(thm)], ['2', '5'])).
% 8.17/8.41  thf(t24_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i,C:$i]:
% 8.17/8.41     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 8.17/8.41       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 8.17/8.41  thf('7', plain,
% 8.17/8.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 8.17/8.41              (k2_xboole_0 @ X18 @ X20)))),
% 8.17/8.41      inference('cnf', [status(esa)], [t24_xboole_1])).
% 8.17/8.41  thf('8', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['6', '7'])).
% 8.17/8.41  thf(t71_xboole_1, conjecture,
% 8.17/8.41    (![A:$i,B:$i,C:$i]:
% 8.17/8.41     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 8.17/8.41         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 8.17/8.41       ( ( A ) = ( C ) ) ))).
% 8.17/8.41  thf(zf_stmt_0, negated_conjecture,
% 8.17/8.41    (~( ![A:$i,B:$i,C:$i]:
% 8.17/8.41        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 8.17/8.41            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 8.17/8.41          ( ( A ) = ( C ) ) ) )),
% 8.17/8.41    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 8.17/8.41  thf('9', plain,
% 8.17/8.41      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C_2 @ sk_B))),
% 8.17/8.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.17/8.41  thf('10', plain,
% 8.17/8.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 8.17/8.41              (k2_xboole_0 @ X18 @ X20)))),
% 8.17/8.41      inference('cnf', [status(esa)], [t24_xboole_1])).
% 8.17/8.41  thf('11', plain,
% 8.17/8.41      (![X0 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ X0) @ 
% 8.17/8.41              (k2_xboole_0 @ sk_A @ sk_B)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['9', '10'])).
% 8.17/8.41  thf('12', plain,
% 8.17/8.41      (((k2_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ sk_A @ sk_B))
% 8.17/8.41         = (k2_xboole_0 @ sk_A @ 
% 8.17/8.41            (k3_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['8', '11'])).
% 8.17/8.41  thf('13', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 8.17/8.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.17/8.41  thf(t3_xboole_0, axiom,
% 8.17/8.41    (![A:$i,B:$i]:
% 8.17/8.41     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 8.17/8.41            ( r1_xboole_0 @ A @ B ) ) ) & 
% 8.17/8.41       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 8.17/8.41            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 8.17/8.41  thf('14', plain,
% 8.17/8.41      (![X1 : $i, X2 : $i]:
% 8.17/8.41         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 8.17/8.41      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.17/8.41  thf(t4_xboole_0, axiom,
% 8.17/8.41    (![A:$i,B:$i]:
% 8.17/8.41     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 8.17/8.41            ( r1_xboole_0 @ A @ B ) ) ) & 
% 8.17/8.41       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 8.17/8.41            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 8.17/8.41  thf('15', plain,
% 8.17/8.41      (![X5 : $i, X7 : $i, X8 : $i]:
% 8.17/8.41         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 8.17/8.41          | ~ (r1_xboole_0 @ X5 @ X8))),
% 8.17/8.41      inference('cnf', [status(esa)], [t4_xboole_0])).
% 8.17/8.41  thf('16', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.17/8.41         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 8.17/8.41          | ~ (r1_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['14', '15'])).
% 8.17/8.41  thf('17', plain,
% 8.17/8.41      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)),
% 8.17/8.41      inference('sup-', [status(thm)], ['13', '16'])).
% 8.17/8.41  thf(t66_xboole_1, axiom,
% 8.17/8.41    (![A:$i]:
% 8.17/8.41     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 8.17/8.41       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 8.17/8.41  thf('18', plain,
% 8.17/8.41      (![X39 : $i]: (((X39) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X39 @ X39))),
% 8.17/8.41      inference('cnf', [status(esa)], [t66_xboole_1])).
% 8.17/8.41  thf('19', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['17', '18'])).
% 8.17/8.41  thf(t3_boole, axiom,
% 8.17/8.41    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.17/8.41  thf('20', plain, (![X32 : $i]: ((k4_xboole_0 @ X32 @ k1_xboole_0) = (X32))),
% 8.17/8.41      inference('cnf', [status(esa)], [t3_boole])).
% 8.17/8.41  thf('21', plain,
% 8.17/8.41      (![X25 : $i, X26 : $i]: (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X25)),
% 8.17/8.41      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.17/8.41  thf('22', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.17/8.41      inference('sup+', [status(thm)], ['20', '21'])).
% 8.17/8.41  thf(t37_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i]:
% 8.17/8.41     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.17/8.41  thf('23', plain,
% 8.17/8.41      (![X27 : $i, X29 : $i]:
% 8.17/8.41         (((k4_xboole_0 @ X27 @ X29) = (k1_xboole_0))
% 8.17/8.41          | ~ (r1_tarski @ X27 @ X29))),
% 8.17/8.41      inference('cnf', [status(esa)], [t37_xboole_1])).
% 8.17/8.41  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['22', '23'])).
% 8.17/8.41  thf('25', plain,
% 8.17/8.41      (![X30 : $i, X31 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30))
% 8.17/8.41           = (k2_xboole_0 @ X30 @ X31))),
% 8.17/8.41      inference('cnf', [status(esa)], [t39_xboole_1])).
% 8.17/8.41  thf('26', plain,
% 8.17/8.41      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 8.17/8.41      inference('sup+', [status(thm)], ['24', '25'])).
% 8.17/8.41  thf(idempotence_k2_xboole_0, axiom,
% 8.17/8.41    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 8.17/8.41  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 8.17/8.41      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 8.17/8.41  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['26', '27'])).
% 8.17/8.41  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 8.17/8.41      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 8.17/8.41  thf(t31_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i,C:$i]:
% 8.17/8.41     ( r1_tarski @
% 8.17/8.41       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 8.17/8.41       ( k2_xboole_0 @ B @ C ) ))).
% 8.17/8.41  thf('30', plain,
% 8.17/8.41      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.17/8.41         (r1_tarski @ 
% 8.17/8.41          (k2_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ (k3_xboole_0 @ X22 @ X24)) @ 
% 8.17/8.41          (k2_xboole_0 @ X23 @ X24))),
% 8.17/8.41      inference('cnf', [status(esa)], [t31_xboole_1])).
% 8.17/8.41  thf('31', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 8.17/8.41      inference('sup+', [status(thm)], ['29', '30'])).
% 8.17/8.41  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 8.17/8.41      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 8.17/8.41  thf('33', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 8.17/8.41      inference('demod', [status(thm)], ['31', '32'])).
% 8.17/8.41  thf('34', plain,
% 8.17/8.41      (![X36 : $i, X37 : $i]:
% 8.17/8.41         (((X37) = (k2_xboole_0 @ X36 @ X37)) | ~ (r1_tarski @ X36 @ X37))),
% 8.17/8.41      inference('demod', [status(thm)], ['3', '4'])).
% 8.17/8.41  thf('35', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['33', '34'])).
% 8.17/8.41  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['26', '27'])).
% 8.17/8.41  thf('37', plain,
% 8.17/8.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 8.17/8.41              (k2_xboole_0 @ X18 @ X20)))),
% 8.17/8.41      inference('cnf', [status(esa)], [t24_xboole_1])).
% 8.17/8.41  thf('38', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 8.17/8.41      inference('sup+', [status(thm)], ['36', '37'])).
% 8.17/8.41  thf(t2_boole, axiom,
% 8.17/8.41    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 8.17/8.41  thf('39', plain,
% 8.17/8.41      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 8.17/8.41      inference('cnf', [status(esa)], [t2_boole])).
% 8.17/8.41  thf('40', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['26', '27'])).
% 8.17/8.41  thf('41', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((X0) = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['38', '39', '40'])).
% 8.17/8.41  thf('42', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((k3_xboole_0 @ X1 @ X0)
% 8.17/8.41           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['35', '41'])).
% 8.17/8.41  thf('43', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.17/8.41      inference('sup+', [status(thm)], ['20', '21'])).
% 8.17/8.41  thf(t18_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i,C:$i]:
% 8.17/8.41     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 8.17/8.41  thf('44', plain,
% 8.17/8.41      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.17/8.41         ((r1_tarski @ X12 @ X13)
% 8.17/8.41          | ~ (r1_tarski @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 8.17/8.41      inference('cnf', [status(esa)], [t18_xboole_1])).
% 8.17/8.41  thf('45', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 8.17/8.41      inference('sup-', [status(thm)], ['43', '44'])).
% 8.17/8.41  thf('46', plain,
% 8.17/8.41      (![X36 : $i, X37 : $i]:
% 8.17/8.41         (((X37) = (k2_xboole_0 @ X36 @ X37)) | ~ (r1_tarski @ X36 @ X37))),
% 8.17/8.41      inference('demod', [status(thm)], ['3', '4'])).
% 8.17/8.41  thf('47', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((X0) = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['45', '46'])).
% 8.17/8.41  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['26', '27'])).
% 8.17/8.41  thf('49', plain,
% 8.17/8.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 8.17/8.41              (k2_xboole_0 @ X18 @ X20)))),
% 8.17/8.41      inference('cnf', [status(esa)], [t24_xboole_1])).
% 8.17/8.41  thf('50', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))
% 8.17/8.41           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['48', '49'])).
% 8.17/8.41  thf('51', plain,
% 8.17/8.41      (![X38 : $i]: ((r1_xboole_0 @ X38 @ X38) | ((X38) != (k1_xboole_0)))),
% 8.17/8.41      inference('cnf', [status(esa)], [t66_xboole_1])).
% 8.17/8.41  thf('52', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 8.17/8.41      inference('simplify', [status(thm)], ['51'])).
% 8.17/8.41  thf('53', plain,
% 8.17/8.41      (![X1 : $i, X2 : $i]:
% 8.17/8.41         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 8.17/8.41      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.17/8.41  thf('54', plain,
% 8.17/8.41      (![X21 : $i]: ((k3_xboole_0 @ X21 @ k1_xboole_0) = (k1_xboole_0))),
% 8.17/8.41      inference('cnf', [status(esa)], [t2_boole])).
% 8.17/8.41  thf('55', plain,
% 8.17/8.41      (![X5 : $i, X7 : $i, X8 : $i]:
% 8.17/8.41         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 8.17/8.41          | ~ (r1_xboole_0 @ X5 @ X8))),
% 8.17/8.41      inference('cnf', [status(esa)], [t4_xboole_0])).
% 8.17/8.41  thf('56', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['54', '55'])).
% 8.17/8.41  thf('57', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['53', '56'])).
% 8.17/8.41  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 8.17/8.41      inference('sup-', [status(thm)], ['52', '57'])).
% 8.17/8.41  thf('59', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.17/8.41         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 8.17/8.41          | ~ (r1_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['14', '15'])).
% 8.17/8.41  thf('60', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ X1)),
% 8.17/8.41      inference('sup-', [status(thm)], ['58', '59'])).
% 8.17/8.41  thf('61', plain,
% 8.17/8.41      (![X39 : $i]: (((X39) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X39 @ X39))),
% 8.17/8.41      inference('cnf', [status(esa)], [t66_xboole_1])).
% 8.17/8.41  thf('62', plain,
% 8.17/8.41      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['60', '61'])).
% 8.17/8.41  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['26', '27'])).
% 8.17/8.41  thf('64', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 8.17/8.41      inference('demod', [status(thm)], ['50', '62', '63'])).
% 8.17/8.41  thf('65', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((k3_xboole_0 @ X0 @ X1)
% 8.17/8.41           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 8.17/8.41      inference('sup+', [status(thm)], ['47', '64'])).
% 8.17/8.41  thf(t16_xboole_1, axiom,
% 8.17/8.41    (![A:$i,B:$i,C:$i]:
% 8.17/8.41     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 8.17/8.41       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 8.17/8.41  thf('66', plain,
% 8.17/8.41      (![X9 : $i, X10 : $i, X11 : $i]:
% 8.17/8.41         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 8.17/8.41           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 8.17/8.41      inference('cnf', [status(esa)], [t16_xboole_1])).
% 8.17/8.41  thf('67', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((k3_xboole_0 @ X0 @ X1)
% 8.17/8.41           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.17/8.41      inference('demod', [status(thm)], ['65', '66'])).
% 8.17/8.41  thf('68', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('sup+', [status(thm)], ['42', '67'])).
% 8.17/8.41  thf('69', plain,
% 8.17/8.41      (((sk_C_2)
% 8.17/8.41         = (k2_xboole_0 @ sk_A @ 
% 8.17/8.41            (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A))))),
% 8.17/8.41      inference('demod', [status(thm)], ['12', '19', '28', '68'])).
% 8.17/8.41  thf('70', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['6', '7'])).
% 8.17/8.41  thf('71', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X1 @ X0)
% 8.17/8.41           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.17/8.41      inference('sup-', [status(thm)], ['2', '5'])).
% 8.17/8.41  thf('72', plain,
% 8.17/8.41      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 8.17/8.41              (k2_xboole_0 @ X18 @ X20)))),
% 8.17/8.41      inference('cnf', [status(esa)], [t24_xboole_1])).
% 8.17/8.41  thf('73', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['71', '72'])).
% 8.17/8.41  thf('74', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 8.17/8.41           = (k2_xboole_0 @ X1 @ (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['70', '73'])).
% 8.17/8.41  thf('75', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 8.17/8.41      inference('demod', [status(thm)], ['50', '62', '63'])).
% 8.17/8.41  thf('76', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('sup+', [status(thm)], ['42', '67'])).
% 8.17/8.41  thf('77', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 8.17/8.41      inference('demod', [status(thm)], ['50', '62', '63'])).
% 8.17/8.41  thf('78', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 8.17/8.41  thf('79', plain,
% 8.17/8.41      (![X0 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ X0 @ sk_B))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ X0) @ 
% 8.17/8.41              (k2_xboole_0 @ sk_A @ sk_B)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['9', '10'])).
% 8.17/8.41  thf('80', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.17/8.41         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 8.17/8.41           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['6', '7'])).
% 8.17/8.41  thf('81', plain,
% 8.17/8.41      (((k2_xboole_0 @ sk_A @ 
% 8.17/8.41         (k3_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B))
% 8.17/8.41         = (k2_xboole_0 @ sk_C_2 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 8.17/8.41      inference('sup+', [status(thm)], ['79', '80'])).
% 8.17/8.41  thf('82', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('sup+', [status(thm)], ['42', '67'])).
% 8.17/8.41  thf('83', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['17', '18'])).
% 8.17/8.41  thf('84', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['26', '27'])).
% 8.17/8.41  thf('85', plain,
% 8.17/8.41      (((k2_xboole_0 @ sk_A @ 
% 8.17/8.41         (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A))) = (sk_C_2))),
% 8.17/8.41      inference('demod', [status(thm)], ['81', '82', '83', '84'])).
% 8.17/8.41  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['22', '23'])).
% 8.17/8.41  thf('87', plain,
% 8.17/8.41      (![X33 : $i, X34 : $i, X35 : $i]:
% 8.17/8.41         ((r1_tarski @ X33 @ (k2_xboole_0 @ X34 @ X35))
% 8.17/8.41          | ~ (r1_tarski @ (k4_xboole_0 @ X33 @ X34) @ X35))),
% 8.17/8.41      inference('cnf', [status(esa)], [t44_xboole_1])).
% 8.17/8.41  thf('88', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]:
% 8.17/8.41         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 8.17/8.41          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.17/8.41      inference('sup-', [status(thm)], ['86', '87'])).
% 8.17/8.41  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['22', '23'])).
% 8.17/8.41  thf('90', plain,
% 8.17/8.41      (![X25 : $i, X26 : $i]: (r1_tarski @ (k4_xboole_0 @ X25 @ X26) @ X25)),
% 8.17/8.41      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.17/8.41  thf('91', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.17/8.41      inference('sup+', [status(thm)], ['89', '90'])).
% 8.17/8.41  thf('92', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['88', '91'])).
% 8.17/8.41  thf('93', plain, ((r1_tarski @ sk_A @ sk_C_2)),
% 8.17/8.41      inference('sup+', [status(thm)], ['85', '92'])).
% 8.17/8.41  thf('94', plain,
% 8.17/8.41      (![X36 : $i, X37 : $i]:
% 8.17/8.41         (((X37) = (k2_xboole_0 @ X36 @ X37)) | ~ (r1_tarski @ X36 @ X37))),
% 8.17/8.41      inference('demod', [status(thm)], ['3', '4'])).
% 8.17/8.41  thf('95', plain, (((sk_C_2) = (k2_xboole_0 @ sk_A @ sk_C_2))),
% 8.17/8.41      inference('sup-', [status(thm)], ['93', '94'])).
% 8.17/8.41  thf('96', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('sup+', [status(thm)], ['42', '67'])).
% 8.17/8.41  thf('97', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 8.17/8.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.17/8.41  thf('98', plain,
% 8.17/8.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.17/8.41         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 8.17/8.41          | ~ (r1_xboole_0 @ X1 @ X0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['14', '15'])).
% 8.17/8.41  thf('99', plain,
% 8.17/8.41      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_B) @ X0)),
% 8.17/8.41      inference('sup-', [status(thm)], ['97', '98'])).
% 8.17/8.41  thf('100', plain,
% 8.17/8.41      (![X39 : $i]: (((X39) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X39 @ X39))),
% 8.17/8.41      inference('cnf', [status(esa)], [t66_xboole_1])).
% 8.17/8.41  thf('101', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 8.17/8.41      inference('sup-', [status(thm)], ['99', '100'])).
% 8.17/8.41  thf('102', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 8.17/8.41      inference('demod', [status(thm)], ['26', '27'])).
% 8.17/8.41  thf('103', plain, (((sk_C_2) = (sk_A))),
% 8.17/8.41      inference('demod', [status(thm)], ['69', '78', '95', '96', '101', '102'])).
% 8.17/8.41  thf('104', plain, (((sk_A) != (sk_C_2))),
% 8.17/8.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.17/8.41  thf('105', plain, ($false),
% 8.17/8.41      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 8.17/8.41  
% 8.17/8.41  % SZS output end Refutation
% 8.17/8.41  
% 8.17/8.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
