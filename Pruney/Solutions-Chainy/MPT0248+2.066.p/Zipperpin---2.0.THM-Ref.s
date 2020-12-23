%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wSaY4gVdVd

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:27 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  179 (1596 expanded)
%              Number of leaves         :   38 ( 481 expanded)
%              Depth                    :   25
%              Number of atoms          : 1227 (17293 expanded)
%              Number of equality atoms :  169 (2737 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

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

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X42 @ X41 )
      | ( X42 = X39 )
      | ( X41
       != ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42 = X39 )
      | ~ ( r2_hidden @ X42 @ ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
      | ( ( sk_C_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X72: $i,X74: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X72 ) @ X74 )
      | ~ ( r2_hidden @ X72 @ X74 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X24: $i] :
      ( ( X22 = X24 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k3_xboole_0 @ X18 @ X21 ) )
      | ~ ( r1_xboole_0 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
      = sk_B_1 )
    | ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_tarski @ X31 @ ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X37 @ X38 ) @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X33 @ X34 ) @ X35 )
      = ( k5_xboole_0 @ X33 @ ( k5_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X36: $i] :
      ( ( k5_xboole_0 @ X36 @ X36 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('33',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('34',plain,(
    ! [X36: $i] :
      ( ( k5_xboole_0 @ X36 @ X36 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['29','35'])).

thf('37',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','36'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_4
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_4
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_4
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_C_4
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
   <= ( sk_C_4
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,
    ( ( ( sk_C_4 != sk_C_4 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_C_4
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_C_4
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_C_4
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('50',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_4
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_C_4
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
      = sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['29','35'])).

thf('56',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_4 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('64',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_C_4
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['49','51','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['48','66'])).

thf('68',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['37','67'])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['37','67'])).

thf('70',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_xboole_0 @ X37 @ X38 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X38 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('71',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_4 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_4 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('73',plain,(
    ! [X36: $i] :
      ( ( k5_xboole_0 @ X36 @ X36 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X33 @ X34 ) @ X35 )
      = ( k5_xboole_0 @ X33 @ ( k5_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_4 )
    = sk_C_4 ),
    inference(demod,[status(thm)],['71','72','79'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('81',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X27 @ X28 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('82',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_xboole_0 @ sk_C_4 @ sk_B_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['29','35'])).

thf('86',plain,
    ( ( k3_xboole_0 @ sk_C_4 @ sk_B_1 )
    = sk_C_4 ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['37','67'])).

thf('89',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('91',plain,(
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('92',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['37','67'])).

thf('98',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['89','98'])).

thf('100',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('101',plain,(
    ! [X39: $i,X42: $i] :
      ( ( X42 = X39 )
      | ~ ( r2_hidden @ X42 @ ( k1_tarski @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['99','109'])).

thf('111',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['89','98'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_C_4 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
      = sk_C_4 ) ),
    inference('sup+',[status(thm)],['86','112'])).

thf('114',plain,
    ( ( sk_C_4 != k1_xboole_0 )
   <= ( sk_C_4 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('115',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('116',plain,(
    ! [X29: $i] :
      ( ( r1_xboole_0 @ X29 @ X29 )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('117',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('119',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('120',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k3_xboole_0 @ X18 @ X21 ) )
      | ~ ( r1_xboole_0 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['115','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['48','66'])).

thf('126',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( sk_C_4 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('128',plain,(
    sk_C_4 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['126','127'])).

thf('129',plain,(
    sk_C_4 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['114','128'])).

thf('130',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
    = sk_C_4 ),
    inference('simplify_reflect-',[status(thm)],['113','129'])).

thf('131',plain,(
    sk_B_1 = sk_C_4 ),
    inference('sup+',[status(thm)],['68','130'])).

thf('132',plain,
    ( ( sk_C_4
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_4
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('133',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( sk_C_4
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) )
   <= ( sk_C_4
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    sk_C_4
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['49','51','65'])).

thf('136',plain,(
    sk_C_4
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_4 ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_4 )
    = sk_B_1 ),
    inference(clc,[status(thm)],['37','67'])).

thf('138',plain,(
    sk_C_4 != sk_B_1 ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['131','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wSaY4gVdVd
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.84/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.07  % Solved by: fo/fo7.sh
% 0.84/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.07  % done 1491 iterations in 0.616s
% 0.84/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.07  % SZS output start Refutation
% 0.84/1.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.84/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.07  thf(sk_B_type, type, sk_B: $i > $i).
% 0.84/1.07  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.84/1.07  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.84/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.84/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.84/1.07  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.84/1.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.07  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.84/1.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.84/1.07  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.84/1.07  thf(t3_xboole_0, axiom,
% 0.84/1.07    (![A:$i,B:$i]:
% 0.84/1.07     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.84/1.07            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.07       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.84/1.07            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.84/1.07  thf('0', plain,
% 0.84/1.07      (![X14 : $i, X15 : $i]:
% 0.84/1.07         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X15))),
% 0.84/1.07      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.07  thf(t43_zfmisc_1, conjecture,
% 0.84/1.07    (![A:$i,B:$i,C:$i]:
% 0.84/1.07     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.84/1.07          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.84/1.07          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.84/1.07          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.84/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.07    (~( ![A:$i,B:$i,C:$i]:
% 0.84/1.07        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.84/1.07             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.84/1.07             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.84/1.07             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.84/1.07    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.84/1.07  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_4))),
% 0.84/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.07  thf(d1_tarski, axiom,
% 0.84/1.07    (![A:$i,B:$i]:
% 0.84/1.07     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.84/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.84/1.07  thf('2', plain,
% 0.84/1.07      (![X39 : $i, X41 : $i, X42 : $i]:
% 0.84/1.07         (~ (r2_hidden @ X42 @ X41)
% 0.84/1.07          | ((X42) = (X39))
% 0.84/1.07          | ((X41) != (k1_tarski @ X39)))),
% 0.84/1.07      inference('cnf', [status(esa)], [d1_tarski])).
% 0.84/1.07  thf('3', plain,
% 0.84/1.07      (![X39 : $i, X42 : $i]:
% 0.84/1.07         (((X42) = (X39)) | ~ (r2_hidden @ X42 @ (k1_tarski @ X39)))),
% 0.84/1.07      inference('simplify', [status(thm)], ['2'])).
% 0.84/1.07  thf('4', plain,
% 0.84/1.07      (![X0 : $i]:
% 0.84/1.07         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))
% 0.84/1.08          | ((X0) = (sk_A)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['1', '3'])).
% 0.84/1.08  thf('5', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))
% 0.84/1.08          | ((sk_C_1 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4) @ X0) = (sk_A)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['0', '4'])).
% 0.84/1.08  thf('6', plain,
% 0.84/1.08      (![X14 : $i, X15 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X14))),
% 0.84/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.08  thf(l1_zfmisc_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.84/1.08  thf('7', plain,
% 0.84/1.08      (![X72 : $i, X74 : $i]:
% 0.84/1.08         ((r1_tarski @ (k1_tarski @ X72) @ X74) | ~ (r2_hidden @ X72 @ X74))),
% 0.84/1.08      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.84/1.08  thf('8', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X0 @ X1)
% 0.84/1.08          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X1 @ X0)) @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['6', '7'])).
% 0.84/1.08  thf('9', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.84/1.08          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))
% 0.84/1.08          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4)))),
% 0.84/1.08      inference('sup+', [status(thm)], ['5', '8'])).
% 0.84/1.08  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_4))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('11', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_4) @ X0)
% 0.84/1.08          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))
% 0.84/1.08          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4)))),
% 0.84/1.08      inference('demod', [status(thm)], ['9', '10'])).
% 0.84/1.08  thf('12', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))
% 0.84/1.08          | (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_4) @ X0))),
% 0.84/1.08      inference('simplify', [status(thm)], ['11'])).
% 0.84/1.08  thf(t7_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.08  thf('13', plain,
% 0.84/1.08      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 0.84/1.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.08  thf(d10_xboole_0, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.84/1.08  thf('14', plain,
% 0.84/1.08      (![X22 : $i, X24 : $i]:
% 0.84/1.08         (((X22) = (X24))
% 0.84/1.08          | ~ (r1_tarski @ X24 @ X22)
% 0.84/1.08          | ~ (r1_tarski @ X22 @ X24))),
% 0.84/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.84/1.08  thf('15', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.84/1.08          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['13', '14'])).
% 0.84/1.08  thf('16', plain,
% 0.84/1.08      (((r1_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))
% 0.84/1.08        | ((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['12', '15'])).
% 0.84/1.08  thf(d1_xboole_0, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.84/1.08  thf('17', plain,
% 0.84/1.08      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.84/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.84/1.08  thf(t4_xboole_0, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.84/1.08            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.84/1.08  thf('18', plain,
% 0.84/1.08      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (r2_hidden @ X20 @ (k3_xboole_0 @ X18 @ X21))
% 0.84/1.08          | ~ (r1_xboole_0 @ X18 @ X21))),
% 0.84/1.08      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.84/1.08  thf('19', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.08  thf('20', plain,
% 0.84/1.08      ((((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1))
% 0.84/1.08        | (v1_xboole_0 @ 
% 0.84/1.08           (k3_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))))),
% 0.84/1.08      inference('sup-', [status(thm)], ['16', '19'])).
% 0.84/1.08  thf('21', plain,
% 0.84/1.08      (![X31 : $i, X32 : $i]: (r1_tarski @ X31 @ (k2_xboole_0 @ X31 @ X32))),
% 0.84/1.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.08  thf(t12_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.84/1.08  thf('22', plain,
% 0.84/1.08      (![X25 : $i, X26 : $i]:
% 0.84/1.08         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.84/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.84/1.08  thf('23', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.84/1.08           = (k2_xboole_0 @ X1 @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['21', '22'])).
% 0.84/1.08  thf(t95_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( k3_xboole_0 @ A @ B ) =
% 0.84/1.08       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.84/1.08  thf('24', plain,
% 0.84/1.08      (![X37 : $i, X38 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X37 @ X38)
% 0.84/1.08           = (k5_xboole_0 @ (k5_xboole_0 @ X37 @ X38) @ 
% 0.84/1.08              (k2_xboole_0 @ X37 @ X38)))),
% 0.84/1.08      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.84/1.08  thf(t91_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i,C:$i]:
% 0.84/1.08     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.84/1.08       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.84/1.08  thf('25', plain,
% 0.84/1.08      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.84/1.08         ((k5_xboole_0 @ (k5_xboole_0 @ X33 @ X34) @ X35)
% 0.84/1.08           = (k5_xboole_0 @ X33 @ (k5_xboole_0 @ X34 @ X35)))),
% 0.84/1.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.84/1.08  thf('26', plain,
% 0.84/1.08      (![X37 : $i, X38 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X37 @ X38)
% 0.84/1.08           = (k5_xboole_0 @ X37 @ 
% 0.84/1.08              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 0.84/1.08      inference('demod', [status(thm)], ['24', '25'])).
% 0.84/1.08  thf('27', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.84/1.08           = (k5_xboole_0 @ X1 @ 
% 0.84/1.08              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 0.84/1.08      inference('sup+', [status(thm)], ['23', '26'])).
% 0.84/1.08  thf(t92_xboole_1, axiom,
% 0.84/1.08    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.84/1.08  thf('28', plain, (![X36 : $i]: ((k5_xboole_0 @ X36 @ X36) = (k1_xboole_0))),
% 0.84/1.08      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.84/1.08  thf('29', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.84/1.08           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.84/1.08      inference('demod', [status(thm)], ['27', '28'])).
% 0.84/1.08  thf(idempotence_k2_xboole_0, axiom,
% 0.84/1.08    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.84/1.08  thf('30', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ X12) = (X12))),
% 0.84/1.08      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.84/1.08  thf('31', plain,
% 0.84/1.08      (![X37 : $i, X38 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X37 @ X38)
% 0.84/1.08           = (k5_xboole_0 @ X37 @ 
% 0.84/1.08              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 0.84/1.08      inference('demod', [status(thm)], ['24', '25'])).
% 0.84/1.08  thf('32', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X0 @ X0)
% 0.84/1.08           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.84/1.08      inference('sup+', [status(thm)], ['30', '31'])).
% 0.84/1.08  thf(idempotence_k3_xboole_0, axiom,
% 0.84/1.08    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.84/1.08  thf('33', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 0.84/1.08      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.84/1.08  thf('34', plain, (![X36 : $i]: ((k5_xboole_0 @ X36 @ X36) = (k1_xboole_0))),
% 0.84/1.08      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.84/1.08  thf('35', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.08      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.84/1.08  thf('36', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.84/1.08      inference('demod', [status(thm)], ['29', '35'])).
% 0.84/1.08  thf('37', plain,
% 0.84/1.08      ((((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.84/1.08      inference('demod', [status(thm)], ['20', '36'])).
% 0.84/1.08  thf(d3_tarski, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( r1_tarski @ A @ B ) <=>
% 0.84/1.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.84/1.08  thf('38', plain,
% 0.84/1.08      (![X6 : $i, X8 : $i]:
% 0.84/1.08         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.84/1.08      inference('cnf', [status(esa)], [d3_tarski])).
% 0.84/1.08  thf('39', plain,
% 0.84/1.08      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.84/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.84/1.08  thf('40', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['38', '39'])).
% 0.84/1.08  thf('41', plain,
% 0.84/1.08      (![X25 : $i, X26 : $i]:
% 0.84/1.08         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.84/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.84/1.08  thf('42', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.08  thf('43', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_4))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('44', plain,
% 0.84/1.08      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_4) != (k1_tarski @ sk_A)))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('45', plain,
% 0.84/1.08      ((((sk_C_4) != (k1_tarski @ sk_A)))
% 0.84/1.08         <= (~ (((sk_C_4) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('split', [status(esa)], ['44'])).
% 0.84/1.08  thf('46', plain,
% 0.84/1.08      ((((sk_C_4) != (k2_xboole_0 @ sk_B_1 @ sk_C_4)))
% 0.84/1.08         <= (~ (((sk_C_4) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('sup-', [status(thm)], ['43', '45'])).
% 0.84/1.08  thf('47', plain,
% 0.84/1.08      (((((sk_C_4) != (sk_C_4)) | ~ (v1_xboole_0 @ sk_B_1)))
% 0.84/1.08         <= (~ (((sk_C_4) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('sup-', [status(thm)], ['42', '46'])).
% 0.84/1.08  thf('48', plain,
% 0.84/1.08      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_C_4) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('simplify', [status(thm)], ['47'])).
% 0.84/1.08  thf('49', plain,
% 0.84/1.08      (~ (((sk_C_4) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.84/1.08      inference('split', [status(esa)], ['44'])).
% 0.84/1.08  thf('50', plain,
% 0.84/1.08      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_4) != (k1_tarski @ sk_A)))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('51', plain,
% 0.84/1.08      (~ (((sk_C_4) = (k1_tarski @ sk_A))) | 
% 0.84/1.08       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.84/1.08      inference('split', [status(esa)], ['50'])).
% 0.84/1.08  thf('52', plain,
% 0.84/1.08      (((r1_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))
% 0.84/1.08        | ((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['12', '15'])).
% 0.84/1.08  thf(d7_xboole_0, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.84/1.08       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.84/1.08  thf('53', plain,
% 0.84/1.08      (![X9 : $i, X10 : $i]:
% 0.84/1.08         (((k3_xboole_0 @ X9 @ X10) = (k1_xboole_0))
% 0.84/1.08          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.84/1.08      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.84/1.08  thf('54', plain,
% 0.84/1.08      ((((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1))
% 0.84/1.08        | ((k3_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_C_4))
% 0.84/1.08            = (k1_xboole_0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['52', '53'])).
% 0.84/1.08  thf('55', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.84/1.08      inference('demod', [status(thm)], ['29', '35'])).
% 0.84/1.08  thf('56', plain,
% 0.84/1.08      ((((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1))
% 0.84/1.08        | ((sk_B_1) = (k1_xboole_0)))),
% 0.84/1.08      inference('demod', [status(thm)], ['54', '55'])).
% 0.84/1.08  thf('57', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_4))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('58', plain,
% 0.84/1.08      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_4) != (k1_xboole_0)))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('59', plain,
% 0.84/1.08      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.84/1.08         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('split', [status(esa)], ['58'])).
% 0.84/1.08  thf('60', plain,
% 0.84/1.08      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_4)))
% 0.84/1.08         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('sup-', [status(thm)], ['57', '59'])).
% 0.84/1.08  thf('61', plain,
% 0.84/1.08      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.84/1.08         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('sup-', [status(thm)], ['56', '60'])).
% 0.84/1.08  thf('62', plain,
% 0.84/1.08      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('simplify', [status(thm)], ['61'])).
% 0.84/1.08  thf('63', plain,
% 0.84/1.08      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.84/1.08      inference('split', [status(esa)], ['44'])).
% 0.84/1.08  thf('64', plain,
% 0.84/1.08      ((((sk_B_1) != (sk_B_1)))
% 0.84/1.08         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.84/1.08             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('sup-', [status(thm)], ['62', '63'])).
% 0.84/1.08  thf('65', plain,
% 0.84/1.08      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.84/1.08      inference('simplify', [status(thm)], ['64'])).
% 0.84/1.08  thf('66', plain, (~ (((sk_C_4) = (k1_tarski @ sk_A)))),
% 0.84/1.08      inference('sat_resolution*', [status(thm)], ['49', '51', '65'])).
% 0.84/1.08  thf('67', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.84/1.08      inference('simpl_trail', [status(thm)], ['48', '66'])).
% 0.84/1.08  thf('68', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1))),
% 0.84/1.08      inference('clc', [status(thm)], ['37', '67'])).
% 0.84/1.08  thf('69', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1))),
% 0.84/1.08      inference('clc', [status(thm)], ['37', '67'])).
% 0.84/1.08  thf('70', plain,
% 0.84/1.08      (![X37 : $i, X38 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X37 @ X38)
% 0.84/1.08           = (k5_xboole_0 @ X37 @ 
% 0.84/1.08              (k5_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X38))))),
% 0.84/1.08      inference('demod', [status(thm)], ['24', '25'])).
% 0.84/1.08  thf('71', plain,
% 0.84/1.08      (((k3_xboole_0 @ sk_B_1 @ sk_C_4)
% 0.84/1.08         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_4 @ sk_B_1)))),
% 0.84/1.08      inference('sup+', [status(thm)], ['69', '70'])).
% 0.84/1.08  thf(commutativity_k5_xboole_0, axiom,
% 0.84/1.08    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.84/1.08  thf('72', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.84/1.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.08  thf('73', plain, (![X36 : $i]: ((k5_xboole_0 @ X36 @ X36) = (k1_xboole_0))),
% 0.84/1.08      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.84/1.08  thf('74', plain,
% 0.84/1.08      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.84/1.08         ((k5_xboole_0 @ (k5_xboole_0 @ X33 @ X34) @ X35)
% 0.84/1.08           = (k5_xboole_0 @ X33 @ (k5_xboole_0 @ X34 @ X35)))),
% 0.84/1.08      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.84/1.08  thf('75', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.84/1.08           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.08      inference('sup+', [status(thm)], ['73', '74'])).
% 0.84/1.08  thf('76', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.84/1.08      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.84/1.08  thf('77', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.84/1.08      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.84/1.08  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.84/1.08      inference('sup+', [status(thm)], ['76', '77'])).
% 0.84/1.08  thf('79', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.84/1.08      inference('demod', [status(thm)], ['75', '78'])).
% 0.84/1.08  thf('80', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_C_4))),
% 0.84/1.08      inference('demod', [status(thm)], ['71', '72', '79'])).
% 0.84/1.08  thf(t17_xboole_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.84/1.08  thf('81', plain,
% 0.84/1.08      (![X27 : $i, X28 : $i]: (r1_tarski @ (k3_xboole_0 @ X27 @ X28) @ X27)),
% 0.84/1.08      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.84/1.08  thf('82', plain,
% 0.84/1.08      (![X25 : $i, X26 : $i]:
% 0.84/1.08         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.84/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.84/1.08  thf('83', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['81', '82'])).
% 0.84/1.08  thf('84', plain, (((k2_xboole_0 @ sk_C_4 @ sk_B_1) = (sk_B_1))),
% 0.84/1.08      inference('sup+', [status(thm)], ['80', '83'])).
% 0.84/1.08  thf('85', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.84/1.08      inference('demod', [status(thm)], ['29', '35'])).
% 0.84/1.08  thf('86', plain, (((k3_xboole_0 @ sk_C_4 @ sk_B_1) = (sk_C_4))),
% 0.84/1.08      inference('sup+', [status(thm)], ['84', '85'])).
% 0.84/1.08  thf('87', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_4))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('88', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1))),
% 0.84/1.08      inference('clc', [status(thm)], ['37', '67'])).
% 0.84/1.08  thf('89', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.84/1.08      inference('demod', [status(thm)], ['87', '88'])).
% 0.84/1.08  thf('90', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_4))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf(t69_enumset1, axiom,
% 0.84/1.08    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.84/1.08  thf('91', plain,
% 0.84/1.08      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.84/1.08      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.84/1.08  thf(l51_zfmisc_1, axiom,
% 0.84/1.08    (![A:$i,B:$i]:
% 0.84/1.08     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.08  thf('92', plain,
% 0.84/1.08      (![X75 : $i, X76 : $i]:
% 0.84/1.08         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 0.84/1.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.84/1.08  thf('93', plain,
% 0.84/1.08      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.84/1.08      inference('sup+', [status(thm)], ['91', '92'])).
% 0.84/1.08  thf('94', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ X12) = (X12))),
% 0.84/1.08      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.84/1.08  thf('95', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.84/1.08      inference('demod', [status(thm)], ['93', '94'])).
% 0.84/1.08  thf('96', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_4)) = (sk_A))),
% 0.84/1.08      inference('sup+', [status(thm)], ['90', '95'])).
% 0.84/1.08  thf('97', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1))),
% 0.84/1.08      inference('clc', [status(thm)], ['37', '67'])).
% 0.84/1.08  thf('98', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.84/1.08      inference('demod', [status(thm)], ['96', '97'])).
% 0.84/1.08  thf('99', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.84/1.08      inference('demod', [status(thm)], ['89', '98'])).
% 0.84/1.08  thf('100', plain,
% 0.84/1.08      (![X14 : $i, X15 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X14 @ X15) | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ X15))),
% 0.84/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.08  thf('101', plain,
% 0.84/1.08      (![X39 : $i, X42 : $i]:
% 0.84/1.08         (((X42) = (X39)) | ~ (r2_hidden @ X42 @ (k1_tarski @ X39)))),
% 0.84/1.08      inference('simplify', [status(thm)], ['2'])).
% 0.84/1.08  thf('102', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.84/1.08          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['100', '101'])).
% 0.84/1.08  thf('103', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X0 @ X1)
% 0.84/1.08          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X1 @ X0)) @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['6', '7'])).
% 0.84/1.08  thf('104', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.84/1.08          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.84/1.08          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.84/1.08      inference('sup+', [status(thm)], ['102', '103'])).
% 0.84/1.08  thf('105', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.84/1.08          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.84/1.08      inference('simplify', [status(thm)], ['104'])).
% 0.84/1.08  thf('106', plain,
% 0.84/1.08      (![X25 : $i, X26 : $i]:
% 0.84/1.08         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 0.84/1.08      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.84/1.08  thf('107', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.84/1.08          | ((k2_xboole_0 @ (k1_tarski @ X1) @ X0) = (X0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['105', '106'])).
% 0.84/1.08  thf('108', plain,
% 0.84/1.08      (![X9 : $i, X10 : $i]:
% 0.84/1.08         (((k3_xboole_0 @ X9 @ X10) = (k1_xboole_0))
% 0.84/1.08          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.84/1.08      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.84/1.08  thf('109', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         (((k2_xboole_0 @ (k1_tarski @ X0) @ X1) = (X1))
% 0.84/1.08          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['107', '108'])).
% 0.84/1.08  thf('110', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         (((k3_xboole_0 @ X0 @ sk_B_1) = (k1_xboole_0))
% 0.84/1.08          | ((k2_xboole_0 @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ X0) = (X0)))),
% 0.84/1.08      inference('sup+', [status(thm)], ['99', '109'])).
% 0.84/1.08  thf('111', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.84/1.08      inference('demod', [status(thm)], ['89', '98'])).
% 0.84/1.08  thf('112', plain,
% 0.84/1.08      (![X0 : $i]:
% 0.84/1.08         (((k3_xboole_0 @ X0 @ sk_B_1) = (k1_xboole_0))
% 0.84/1.08          | ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))),
% 0.84/1.08      inference('demod', [status(thm)], ['110', '111'])).
% 0.84/1.08  thf('113', plain,
% 0.84/1.08      ((((sk_C_4) = (k1_xboole_0))
% 0.84/1.08        | ((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_C_4)))),
% 0.84/1.08      inference('sup+', [status(thm)], ['86', '112'])).
% 0.84/1.08  thf('114', plain,
% 0.84/1.08      ((((sk_C_4) != (k1_xboole_0))) <= (~ (((sk_C_4) = (k1_xboole_0))))),
% 0.84/1.08      inference('split', [status(esa)], ['58'])).
% 0.84/1.08  thf('115', plain,
% 0.84/1.08      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('simplify', [status(thm)], ['61'])).
% 0.84/1.08  thf(t66_xboole_1, axiom,
% 0.84/1.08    (![A:$i]:
% 0.84/1.08     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.84/1.08       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.84/1.08  thf('116', plain,
% 0.84/1.08      (![X29 : $i]: ((r1_xboole_0 @ X29 @ X29) | ((X29) != (k1_xboole_0)))),
% 0.84/1.08      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.84/1.08  thf('117', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.84/1.08      inference('simplify', [status(thm)], ['116'])).
% 0.84/1.08  thf('118', plain,
% 0.84/1.08      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.84/1.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.84/1.08  thf('119', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 0.84/1.08      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.84/1.08  thf('120', plain,
% 0.84/1.08      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.84/1.08         (~ (r2_hidden @ X20 @ (k3_xboole_0 @ X18 @ X21))
% 0.84/1.08          | ~ (r1_xboole_0 @ X18 @ X21))),
% 0.84/1.08      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.84/1.08  thf('121', plain,
% 0.84/1.08      (![X0 : $i, X1 : $i]:
% 0.84/1.08         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['119', '120'])).
% 0.84/1.08  thf('122', plain,
% 0.84/1.08      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.84/1.08      inference('sup-', [status(thm)], ['118', '121'])).
% 0.84/1.08  thf('123', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.84/1.08      inference('sup-', [status(thm)], ['117', '122'])).
% 0.84/1.08  thf('124', plain,
% 0.84/1.08      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('sup+', [status(thm)], ['115', '123'])).
% 0.84/1.08  thf('125', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.84/1.08      inference('simpl_trail', [status(thm)], ['48', '66'])).
% 0.84/1.08  thf('126', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.84/1.08      inference('sup-', [status(thm)], ['124', '125'])).
% 0.84/1.08  thf('127', plain,
% 0.84/1.08      (~ (((sk_C_4) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.84/1.08      inference('split', [status(esa)], ['58'])).
% 0.84/1.08  thf('128', plain, (~ (((sk_C_4) = (k1_xboole_0)))),
% 0.84/1.08      inference('sat_resolution*', [status(thm)], ['126', '127'])).
% 0.84/1.08  thf('129', plain, (((sk_C_4) != (k1_xboole_0))),
% 0.84/1.08      inference('simpl_trail', [status(thm)], ['114', '128'])).
% 0.84/1.08  thf('130', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_C_4))),
% 0.84/1.08      inference('simplify_reflect-', [status(thm)], ['113', '129'])).
% 0.84/1.08  thf('131', plain, (((sk_B_1) = (sk_C_4))),
% 0.84/1.08      inference('sup+', [status(thm)], ['68', '130'])).
% 0.84/1.08  thf('132', plain,
% 0.84/1.08      ((((sk_C_4) != (k1_tarski @ sk_A)))
% 0.84/1.08         <= (~ (((sk_C_4) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('split', [status(esa)], ['44'])).
% 0.84/1.08  thf('133', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_4))),
% 0.84/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.08  thf('134', plain,
% 0.84/1.08      ((((sk_C_4) != (k2_xboole_0 @ sk_B_1 @ sk_C_4)))
% 0.84/1.08         <= (~ (((sk_C_4) = (k1_tarski @ sk_A))))),
% 0.84/1.08      inference('demod', [status(thm)], ['132', '133'])).
% 0.84/1.08  thf('135', plain, (~ (((sk_C_4) = (k1_tarski @ sk_A)))),
% 0.84/1.08      inference('sat_resolution*', [status(thm)], ['49', '51', '65'])).
% 0.84/1.08  thf('136', plain, (((sk_C_4) != (k2_xboole_0 @ sk_B_1 @ sk_C_4))),
% 0.84/1.08      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 0.84/1.08  thf('137', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_4) = (sk_B_1))),
% 0.84/1.08      inference('clc', [status(thm)], ['37', '67'])).
% 0.84/1.08  thf('138', plain, (((sk_C_4) != (sk_B_1))),
% 0.84/1.08      inference('demod', [status(thm)], ['136', '137'])).
% 0.84/1.08  thf('139', plain, ($false),
% 0.84/1.08      inference('simplify_reflect-', [status(thm)], ['131', '138'])).
% 0.84/1.08  
% 0.84/1.08  % SZS output end Refutation
% 0.84/1.08  
% 0.92/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
