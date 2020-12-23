%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ICjlcuM1y1

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:27 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  204 ( 943 expanded)
%              Number of leaves         :   30 ( 283 expanded)
%              Depth                    :   26
%              Number of atoms          : 1467 (8971 expanded)
%              Number of equality atoms :  231 (1563 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X60 ) @ X62 )
      | ~ ( r2_hidden @ X60 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X60: $i,X61: $i] :
      ( ( r2_hidden @ X60 @ X61 )
      | ~ ( r1_tarski @ ( k1_tarski @ X60 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X66: $i,X67: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X66 ) @ ( k1_tarski @ X67 ) )
        = ( k1_tarski @ X66 ) )
      | ( X66 = X67 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('24',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['19','22','25'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X65: $i,X66: $i] :
      ( ( X66 != X65 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X66 ) @ ( k1_tarski @ X65 ) )
       != ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('32',plain,(
    ! [X65: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X65 ) @ ( k1_tarski @ X65 ) )
     != ( k1_tarski @ X65 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('34',plain,(
    ! [X65: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X65 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(clc,[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['8','35'])).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf('41',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X65: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X65 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','44'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('48',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('49',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('52',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( X30 = X27 )
      | ( X29
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('57',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('60',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X60: $i,X62: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X60 ) @ X62 )
      | ~ ( r2_hidden @ X60 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('63',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('65',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('70',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('71',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('76',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('78',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','80'])).

thf('82',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('83',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_2 )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( ( sk_B @ sk_C_2 )
      = sk_A )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('88',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['89','97'])).

thf('99',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('101',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( sk_B_1 = sk_C_2 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('105',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['105'])).

thf('107',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['105'])).

thf('108',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['108'])).

thf('110',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('111',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['105'])).

thf('116',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['107','109','117'])).

thf('119',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['106','118'])).

thf('120',plain,
    ( ( sk_C_2 != sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','119'])).

thf('121',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['103','120'])).

thf('122',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['98','121'])).

thf('123',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['111'])).

thf('124',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('130',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('132',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k3_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = ( k3_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['138','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('144',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('147',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('148',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('152',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['146','149'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','44'])).

thf('158',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['145','158'])).

thf('160',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('161',plain,
    ( ! [X0: $i] :
        ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('163',plain,
    ( ( sk_C_2
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','161','162'])).

thf('164',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['106','118'])).

thf('165',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['111'])).

thf('167',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['165','166'])).

thf('168',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['125','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['47','168'])).

thf('170',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['0','169'])).

thf('171',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['106','118'])).

thf('172',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['170','171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ICjlcuM1y1
% 0.14/0.37  % Computer   : n013.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 15:12:25 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.98/2.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.98/2.17  % Solved by: fo/fo7.sh
% 1.98/2.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.98/2.17  % done 2593 iterations in 1.683s
% 1.98/2.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.98/2.17  % SZS output start Refutation
% 1.98/2.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.98/2.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.98/2.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.98/2.17  thf(sk_A_type, type, sk_A: $i).
% 1.98/2.17  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.98/2.17  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.98/2.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.98/2.17  thf(sk_B_type, type, sk_B: $i > $i).
% 1.98/2.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.98/2.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.98/2.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.98/2.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.98/2.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.98/2.17  thf(t43_zfmisc_1, conjecture,
% 1.98/2.17    (![A:$i,B:$i,C:$i]:
% 1.98/2.17     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.98/2.17          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.98/2.17          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.98/2.17          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.98/2.17  thf(zf_stmt_0, negated_conjecture,
% 1.98/2.17    (~( ![A:$i,B:$i,C:$i]:
% 1.98/2.17        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.98/2.17             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.98/2.17             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.98/2.17             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.98/2.17    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.98/2.17  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.98/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.17  thf(d3_tarski, axiom,
% 1.98/2.17    (![A:$i,B:$i]:
% 1.98/2.17     ( ( r1_tarski @ A @ B ) <=>
% 1.98/2.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.98/2.17  thf('1', plain,
% 1.98/2.17      (![X3 : $i, X5 : $i]:
% 1.98/2.17         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.98/2.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.98/2.17  thf(l1_zfmisc_1, axiom,
% 1.98/2.17    (![A:$i,B:$i]:
% 1.98/2.17     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.98/2.17  thf('2', plain,
% 1.98/2.17      (![X60 : $i, X62 : $i]:
% 1.98/2.17         ((r1_tarski @ (k1_tarski @ X60) @ X62) | ~ (r2_hidden @ X60 @ X62))),
% 1.98/2.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.98/2.17  thf('3', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((r1_tarski @ X0 @ X1)
% 1.98/2.17          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 1.98/2.17      inference('sup-', [status(thm)], ['1', '2'])).
% 1.98/2.17  thf(d10_xboole_0, axiom,
% 1.98/2.17    (![A:$i,B:$i]:
% 1.98/2.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.98/2.17  thf('4', plain,
% 1.98/2.17      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 1.98/2.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.98/2.17  thf('5', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 1.98/2.17      inference('simplify', [status(thm)], ['4'])).
% 1.98/2.17  thf('6', plain,
% 1.98/2.17      (![X60 : $i, X61 : $i]:
% 1.98/2.17         ((r2_hidden @ X60 @ X61) | ~ (r1_tarski @ (k1_tarski @ X60) @ X61))),
% 1.98/2.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.98/2.17  thf('7', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.98/2.17      inference('sup-', [status(thm)], ['5', '6'])).
% 1.98/2.17  thf('8', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((r1_tarski @ X0 @ X1)
% 1.98/2.17          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 1.98/2.17      inference('sup-', [status(thm)], ['1', '2'])).
% 1.98/2.17  thf(t20_zfmisc_1, axiom,
% 1.98/2.17    (![A:$i,B:$i]:
% 1.98/2.17     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.98/2.17         ( k1_tarski @ A ) ) <=>
% 1.98/2.17       ( ( A ) != ( B ) ) ))).
% 1.98/2.17  thf('9', plain,
% 1.98/2.17      (![X66 : $i, X67 : $i]:
% 1.98/2.17         (((k4_xboole_0 @ (k1_tarski @ X66) @ (k1_tarski @ X67))
% 1.98/2.17            = (k1_tarski @ X66))
% 1.98/2.17          | ((X66) = (X67)))),
% 1.98/2.17      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.98/2.17  thf(t100_xboole_1, axiom,
% 1.98/2.17    (![A:$i,B:$i]:
% 1.98/2.17     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.98/2.17  thf('10', plain,
% 1.98/2.17      (![X12 : $i, X13 : $i]:
% 1.98/2.17         ((k4_xboole_0 @ X12 @ X13)
% 1.98/2.17           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.98/2.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.98/2.17  thf(t92_xboole_1, axiom,
% 1.98/2.17    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.98/2.17  thf('11', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 1.98/2.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.98/2.17  thf(t91_xboole_1, axiom,
% 1.98/2.17    (![A:$i,B:$i,C:$i]:
% 1.98/2.17     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.98/2.17       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.98/2.17  thf('12', plain,
% 1.98/2.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.98/2.17         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 1.98/2.17           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 1.98/2.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.98/2.17  thf('13', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.98/2.17           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['11', '12'])).
% 1.98/2.17  thf(commutativity_k5_xboole_0, axiom,
% 1.98/2.17    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.98/2.17  thf('14', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.98/2.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.98/2.17  thf(t5_boole, axiom,
% 1.98/2.17    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.98/2.17  thf('15', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.98/2.17      inference('cnf', [status(esa)], [t5_boole])).
% 1.98/2.17  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['14', '15'])).
% 1.98/2.17  thf('17', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.98/2.17      inference('demod', [status(thm)], ['13', '16'])).
% 1.98/2.17  thf('18', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((k3_xboole_0 @ X1 @ X0)
% 1.98/2.17           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['10', '17'])).
% 1.98/2.17  thf('19', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         (((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.98/2.17            = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 1.98/2.17          | ((X0) = (X1)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['9', '18'])).
% 1.98/2.17  thf(idempotence_k3_xboole_0, axiom,
% 1.98/2.17    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.98/2.17  thf('20', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 1.98/2.17      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.98/2.17  thf('21', plain,
% 1.98/2.17      (![X12 : $i, X13 : $i]:
% 1.98/2.17         ((k4_xboole_0 @ X12 @ X13)
% 1.98/2.17           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.98/2.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.98/2.17  thf('22', plain,
% 1.98/2.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['20', '21'])).
% 1.98/2.17  thf('23', plain,
% 1.98/2.17      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['20', '21'])).
% 1.98/2.17  thf('24', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 1.98/2.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.98/2.17  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['23', '24'])).
% 1.98/2.17  thf('26', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         (((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) = (k1_xboole_0))
% 1.98/2.17          | ((X0) = (X1)))),
% 1.98/2.17      inference('demod', [status(thm)], ['19', '22', '25'])).
% 1.98/2.17  thf(t17_xboole_1, axiom,
% 1.98/2.17    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.98/2.17  thf('27', plain,
% 1.98/2.17      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 1.98/2.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.98/2.17  thf('28', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['26', '27'])).
% 1.98/2.17  thf('29', plain,
% 1.98/2.17      (![X9 : $i, X11 : $i]:
% 1.98/2.17         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 1.98/2.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.98/2.17  thf('30', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         (((X0) = (X1))
% 1.98/2.17          | ~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 1.98/2.17          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['28', '29'])).
% 1.98/2.17  thf('31', plain,
% 1.98/2.17      (![X65 : $i, X66 : $i]:
% 1.98/2.17         (((X66) != (X65))
% 1.98/2.17          | ((k4_xboole_0 @ (k1_tarski @ X66) @ (k1_tarski @ X65))
% 1.98/2.17              != (k1_tarski @ X66)))),
% 1.98/2.17      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.98/2.17  thf('32', plain,
% 1.98/2.17      (![X65 : $i]:
% 1.98/2.17         ((k4_xboole_0 @ (k1_tarski @ X65) @ (k1_tarski @ X65))
% 1.98/2.17           != (k1_tarski @ X65))),
% 1.98/2.17      inference('simplify', [status(thm)], ['31'])).
% 1.98/2.17  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['23', '24'])).
% 1.98/2.17  thf('34', plain, (![X65 : $i]: ((k1_xboole_0) != (k1_tarski @ X65))),
% 1.98/2.17      inference('demod', [status(thm)], ['32', '33'])).
% 1.98/2.17  thf('35', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0) | ((X0) = (X1)))),
% 1.98/2.17      inference('clc', [status(thm)], ['30', '34'])).
% 1.98/2.17  thf('36', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((r1_tarski @ k1_xboole_0 @ X0) | ((sk_C @ X0 @ k1_xboole_0) = (X1)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['8', '35'])).
% 1.98/2.17  thf('37', plain,
% 1.98/2.17      (![X3 : $i, X5 : $i]:
% 1.98/2.17         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.98/2.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.98/2.17  thf('38', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         (~ (r2_hidden @ X0 @ X1)
% 1.98/2.17          | (r1_tarski @ k1_xboole_0 @ X1)
% 1.98/2.17          | (r1_tarski @ k1_xboole_0 @ X1))),
% 1.98/2.17      inference('sup-', [status(thm)], ['36', '37'])).
% 1.98/2.17  thf('39', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((r1_tarski @ k1_xboole_0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.98/2.17      inference('simplify', [status(thm)], ['38'])).
% 1.98/2.17  thf('40', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 1.98/2.17      inference('sup-', [status(thm)], ['7', '39'])).
% 1.98/2.17  thf('41', plain,
% 1.98/2.17      (![X9 : $i, X11 : $i]:
% 1.98/2.17         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 1.98/2.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.98/2.17  thf('42', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 1.98/2.17          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['40', '41'])).
% 1.98/2.17  thf('43', plain, (![X65 : $i]: ((k1_xboole_0) != (k1_tarski @ X65))),
% 1.98/2.17      inference('demod', [status(thm)], ['32', '33'])).
% 1.98/2.17  thf('44', plain,
% 1.98/2.17      (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)),
% 1.98/2.17      inference('clc', [status(thm)], ['42', '43'])).
% 1.98/2.17  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.98/2.17      inference('sup-', [status(thm)], ['3', '44'])).
% 1.98/2.17  thf(t12_xboole_1, axiom,
% 1.98/2.17    (![A:$i,B:$i]:
% 1.98/2.17     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.98/2.17  thf('46', plain,
% 1.98/2.17      (![X14 : $i, X15 : $i]:
% 1.98/2.17         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 1.98/2.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.98/2.17  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.17      inference('sup-', [status(thm)], ['45', '46'])).
% 1.98/2.17  thf(t7_xboole_0, axiom,
% 1.98/2.17    (![A:$i]:
% 1.98/2.17     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.98/2.17          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.98/2.17  thf('48', plain,
% 1.98/2.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.98/2.17      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.98/2.17  thf('49', plain,
% 1.98/2.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.98/2.17      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.98/2.17  thf('50', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.98/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.17  thf(t7_xboole_1, axiom,
% 1.98/2.17    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.98/2.17  thf('51', plain,
% 1.98/2.17      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 1.98/2.17      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.98/2.17  thf('52', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.98/2.17      inference('sup+', [status(thm)], ['50', '51'])).
% 1.98/2.17  thf('53', plain,
% 1.98/2.17      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.98/2.17         (~ (r2_hidden @ X2 @ X3)
% 1.98/2.17          | (r2_hidden @ X2 @ X4)
% 1.98/2.17          | ~ (r1_tarski @ X3 @ X4))),
% 1.98/2.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.98/2.17  thf('54', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.98/2.17      inference('sup-', [status(thm)], ['52', '53'])).
% 1.98/2.17  thf('55', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))
% 1.98/2.17        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['49', '54'])).
% 1.98/2.17  thf(d1_tarski, axiom,
% 1.98/2.17    (![A:$i,B:$i]:
% 1.98/2.17     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.98/2.17       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.98/2.17  thf('56', plain,
% 1.98/2.17      (![X27 : $i, X29 : $i, X30 : $i]:
% 1.98/2.17         (~ (r2_hidden @ X30 @ X29)
% 1.98/2.17          | ((X30) = (X27))
% 1.98/2.17          | ((X29) != (k1_tarski @ X27)))),
% 1.98/2.17      inference('cnf', [status(esa)], [d1_tarski])).
% 1.98/2.17  thf('57', plain,
% 1.98/2.17      (![X27 : $i, X30 : $i]:
% 1.98/2.17         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 1.98/2.17      inference('simplify', [status(thm)], ['56'])).
% 1.98/2.17  thf('58', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (sk_A)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['55', '57'])).
% 1.98/2.17  thf('59', plain,
% 1.98/2.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.98/2.17      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.98/2.17  thf('60', plain,
% 1.98/2.17      (((r2_hidden @ sk_A @ sk_B_1)
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0))
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['58', '59'])).
% 1.98/2.17  thf('61', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 1.98/2.17      inference('simplify', [status(thm)], ['60'])).
% 1.98/2.17  thf('62', plain,
% 1.98/2.17      (![X60 : $i, X62 : $i]:
% 1.98/2.17         ((r1_tarski @ (k1_tarski @ X60) @ X62) | ~ (r2_hidden @ X60 @ X62))),
% 1.98/2.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.98/2.17  thf('63', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.98/2.17      inference('sup-', [status(thm)], ['61', '62'])).
% 1.98/2.17  thf('64', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.98/2.17      inference('sup+', [status(thm)], ['50', '51'])).
% 1.98/2.17  thf('65', plain,
% 1.98/2.17      (![X9 : $i, X11 : $i]:
% 1.98/2.17         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 1.98/2.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.98/2.17  thf('66', plain,
% 1.98/2.17      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.98/2.17        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['64', '65'])).
% 1.98/2.17  thf('67', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['63', '66'])).
% 1.98/2.17  thf('68', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.98/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.17  thf(t95_xboole_1, axiom,
% 1.98/2.17    (![A:$i,B:$i]:
% 1.98/2.17     ( ( k3_xboole_0 @ A @ B ) =
% 1.98/2.17       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.98/2.17  thf('69', plain,
% 1.98/2.17      (![X25 : $i, X26 : $i]:
% 1.98/2.17         ((k3_xboole_0 @ X25 @ X26)
% 1.98/2.17           = (k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 1.98/2.17              (k2_xboole_0 @ X25 @ X26)))),
% 1.98/2.17      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.98/2.17  thf('70', plain,
% 1.98/2.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.98/2.17         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 1.98/2.17           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 1.98/2.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.98/2.17  thf('71', plain,
% 1.98/2.17      (![X25 : $i, X26 : $i]:
% 1.98/2.17         ((k3_xboole_0 @ X25 @ X26)
% 1.98/2.17           = (k5_xboole_0 @ X25 @ 
% 1.98/2.17              (k5_xboole_0 @ X26 @ (k2_xboole_0 @ X25 @ X26))))),
% 1.98/2.17      inference('demod', [status(thm)], ['69', '70'])).
% 1.98/2.17  thf('72', plain,
% 1.98/2.17      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 1.98/2.17         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup+', [status(thm)], ['68', '71'])).
% 1.98/2.17  thf('73', plain,
% 1.98/2.17      ((((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 1.98/2.17          = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ sk_B_1)))
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['67', '72'])).
% 1.98/2.17  thf('74', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.98/2.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.98/2.17  thf('75', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.98/2.17      inference('demod', [status(thm)], ['13', '16'])).
% 1.98/2.17  thf('76', plain,
% 1.98/2.17      ((((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.98/2.17  thf('77', plain,
% 1.98/2.17      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 1.98/2.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.98/2.17  thf('78', plain,
% 1.98/2.17      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.98/2.17         (~ (r2_hidden @ X2 @ X3)
% 1.98/2.17          | (r2_hidden @ X2 @ X4)
% 1.98/2.17          | ~ (r1_tarski @ X3 @ X4))),
% 1.98/2.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.98/2.17  thf('79', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.98/2.17         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['77', '78'])).
% 1.98/2.17  thf('80', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         (~ (r2_hidden @ X0 @ sk_C_2)
% 1.98/2.17          | ((sk_B_1) = (k1_xboole_0))
% 1.98/2.17          | (r2_hidden @ X0 @ sk_B_1))),
% 1.98/2.17      inference('sup-', [status(thm)], ['76', '79'])).
% 1.98/2.17  thf('81', plain,
% 1.98/2.17      ((((sk_C_2) = (k1_xboole_0))
% 1.98/2.17        | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['48', '80'])).
% 1.98/2.17  thf('82', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['63', '66'])).
% 1.98/2.17  thf('83', plain,
% 1.98/2.17      (![X27 : $i, X30 : $i]:
% 1.98/2.17         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 1.98/2.17      inference('simplify', [status(thm)], ['56'])).
% 1.98/2.17  thf('84', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.98/2.17          | ((sk_B_1) = (k1_xboole_0))
% 1.98/2.17          | ((X0) = (sk_A)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['82', '83'])).
% 1.98/2.17  thf('85', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))
% 1.98/2.17        | ((sk_C_2) = (k1_xboole_0))
% 1.98/2.17        | ((sk_B @ sk_C_2) = (sk_A))
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['81', '84'])).
% 1.98/2.17  thf('86', plain,
% 1.98/2.17      ((((sk_B @ sk_C_2) = (sk_A))
% 1.98/2.17        | ((sk_C_2) = (k1_xboole_0))
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('simplify', [status(thm)], ['85'])).
% 1.98/2.17  thf('87', plain,
% 1.98/2.17      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.98/2.17      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.98/2.17  thf('88', plain,
% 1.98/2.17      (((r2_hidden @ sk_A @ sk_C_2)
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0))
% 1.98/2.17        | ((sk_C_2) = (k1_xboole_0))
% 1.98/2.17        | ((sk_C_2) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['86', '87'])).
% 1.98/2.17  thf('89', plain,
% 1.98/2.17      ((((sk_C_2) = (k1_xboole_0))
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0))
% 1.98/2.17        | (r2_hidden @ sk_A @ sk_C_2))),
% 1.98/2.17      inference('simplify', [status(thm)], ['88'])).
% 1.98/2.17  thf('90', plain,
% 1.98/2.17      (![X3 : $i, X5 : $i]:
% 1.98/2.17         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.98/2.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.98/2.17  thf('91', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.98/2.17      inference('sup-', [status(thm)], ['52', '53'])).
% 1.98/2.17  thf('92', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         ((r1_tarski @ sk_B_1 @ X0)
% 1.98/2.17          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['90', '91'])).
% 1.98/2.17  thf('93', plain,
% 1.98/2.17      (![X27 : $i, X30 : $i]:
% 1.98/2.17         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 1.98/2.17      inference('simplify', [status(thm)], ['56'])).
% 1.98/2.17  thf('94', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['92', '93'])).
% 1.98/2.17  thf('95', plain,
% 1.98/2.17      (![X3 : $i, X5 : $i]:
% 1.98/2.17         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 1.98/2.17      inference('cnf', [status(esa)], [d3_tarski])).
% 1.98/2.17  thf('96', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         (~ (r2_hidden @ sk_A @ X0)
% 1.98/2.17          | (r1_tarski @ sk_B_1 @ X0)
% 1.98/2.17          | (r1_tarski @ sk_B_1 @ X0))),
% 1.98/2.17      inference('sup-', [status(thm)], ['94', '95'])).
% 1.98/2.17  thf('97', plain,
% 1.98/2.17      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 1.98/2.17      inference('simplify', [status(thm)], ['96'])).
% 1.98/2.17  thf('98', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))
% 1.98/2.17        | ((sk_C_2) = (k1_xboole_0))
% 1.98/2.17        | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.98/2.17      inference('sup-', [status(thm)], ['89', '97'])).
% 1.98/2.17  thf('99', plain,
% 1.98/2.17      ((((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))
% 1.98/2.17        | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.98/2.17  thf('100', plain,
% 1.98/2.17      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 1.98/2.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.98/2.17  thf('101', plain,
% 1.98/2.17      (((r1_tarski @ sk_C_2 @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['99', '100'])).
% 1.98/2.17  thf('102', plain,
% 1.98/2.17      (![X9 : $i, X11 : $i]:
% 1.98/2.17         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 1.98/2.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.98/2.17  thf('103', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))
% 1.98/2.17        | ~ (r1_tarski @ sk_B_1 @ sk_C_2)
% 1.98/2.17        | ((sk_B_1) = (sk_C_2)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['101', '102'])).
% 1.98/2.17  thf('104', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['63', '66'])).
% 1.98/2.17  thf('105', plain,
% 1.98/2.17      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.17  thf('106', plain,
% 1.98/2.17      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 1.98/2.17         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('split', [status(esa)], ['105'])).
% 1.98/2.17  thf('107', plain,
% 1.98/2.17      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('split', [status(esa)], ['105'])).
% 1.98/2.17  thf('108', plain,
% 1.98/2.17      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.17  thf('109', plain,
% 1.98/2.17      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 1.98/2.17       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('split', [status(esa)], ['108'])).
% 1.98/2.17  thf('110', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['63', '66'])).
% 1.98/2.17  thf('111', plain,
% 1.98/2.17      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 1.98/2.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.17  thf('112', plain,
% 1.98/2.17      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('split', [status(esa)], ['111'])).
% 1.98/2.17  thf('113', plain,
% 1.98/2.17      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup-', [status(thm)], ['110', '112'])).
% 1.98/2.17  thf('114', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('simplify', [status(thm)], ['113'])).
% 1.98/2.17  thf('115', plain,
% 1.98/2.17      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.98/2.17      inference('split', [status(esa)], ['105'])).
% 1.98/2.17  thf('116', plain,
% 1.98/2.17      ((((sk_B_1) != (sk_B_1)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.98/2.17             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup-', [status(thm)], ['114', '115'])).
% 1.98/2.17  thf('117', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('simplify', [status(thm)], ['116'])).
% 1.98/2.17  thf('118', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('sat_resolution*', [status(thm)], ['107', '109', '117'])).
% 1.98/2.17  thf('119', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 1.98/2.17      inference('simpl_trail', [status(thm)], ['106', '118'])).
% 1.98/2.17  thf('120', plain, ((((sk_C_2) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['104', '119'])).
% 1.98/2.17  thf('121', plain,
% 1.98/2.17      ((~ (r1_tarski @ sk_B_1 @ sk_C_2) | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('clc', [status(thm)], ['103', '120'])).
% 1.98/2.17  thf('122', plain,
% 1.98/2.17      ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 1.98/2.17      inference('clc', [status(thm)], ['98', '121'])).
% 1.98/2.17  thf('123', plain,
% 1.98/2.17      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.98/2.17      inference('split', [status(esa)], ['111'])).
% 1.98/2.17  thf('124', plain,
% 1.98/2.17      (((((sk_C_2) != (sk_C_2)) | ((sk_B_1) = (k1_xboole_0))))
% 1.98/2.17         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.98/2.17      inference('sup-', [status(thm)], ['122', '123'])).
% 1.98/2.17  thf('125', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.98/2.17      inference('simplify', [status(thm)], ['124'])).
% 1.98/2.17  thf('126', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('simplify', [status(thm)], ['113'])).
% 1.98/2.17  thf('127', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['14', '15'])).
% 1.98/2.17  thf('128', plain,
% 1.98/2.17      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup+', [status(thm)], ['126', '127'])).
% 1.98/2.17  thf('129', plain,
% 1.98/2.17      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 1.98/2.17         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup+', [status(thm)], ['68', '71'])).
% 1.98/2.17  thf('130', plain,
% 1.98/2.17      ((((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 1.98/2.17          = (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup+', [status(thm)], ['128', '129'])).
% 1.98/2.17  thf('131', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('simplify', [status(thm)], ['113'])).
% 1.98/2.17  thf('132', plain,
% 1.98/2.17      (![X12 : $i, X13 : $i]:
% 1.98/2.17         ((k4_xboole_0 @ X12 @ X13)
% 1.98/2.17           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.98/2.17      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.98/2.17  thf('133', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['14', '15'])).
% 1.98/2.17  thf('134', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['132', '133'])).
% 1.98/2.17  thf('135', plain,
% 1.98/2.17      ((![X0 : $i]:
% 1.98/2.17          ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ sk_B_1 @ X0)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup+', [status(thm)], ['131', '134'])).
% 1.98/2.17  thf('136', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('simplify', [status(thm)], ['113'])).
% 1.98/2.17  thf('137', plain,
% 1.98/2.17      ((![X0 : $i]: ((k4_xboole_0 @ sk_B_1 @ X0) = (k3_xboole_0 @ sk_B_1 @ X0)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('demod', [status(thm)], ['135', '136'])).
% 1.98/2.17  thf('138', plain,
% 1.98/2.17      ((((k4_xboole_0 @ sk_B_1 @ sk_C_2)
% 1.98/2.17          = (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('demod', [status(thm)], ['130', '137'])).
% 1.98/2.17  thf('139', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.98/2.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.98/2.17  thf('140', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.98/2.17      inference('demod', [status(thm)], ['13', '16'])).
% 1.98/2.17  thf('141', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.98/2.17      inference('sup+', [status(thm)], ['139', '140'])).
% 1.98/2.17  thf('142', plain,
% 1.98/2.17      ((((sk_C_2)
% 1.98/2.17          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ sk_B_1 @ sk_C_2))))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup+', [status(thm)], ['138', '141'])).
% 1.98/2.17  thf('143', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.98/2.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.98/2.17  thf('144', plain,
% 1.98/2.17      ((((sk_C_2)
% 1.98/2.17          = (k5_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2) @ (k1_tarski @ sk_A))))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('demod', [status(thm)], ['142', '143'])).
% 1.98/2.17  thf('145', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('simplify', [status(thm)], ['113'])).
% 1.98/2.17  thf('146', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['132', '133'])).
% 1.98/2.17  thf('147', plain,
% 1.98/2.17      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 1.98/2.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.98/2.17  thf('148', plain,
% 1.98/2.17      (![X14 : $i, X15 : $i]:
% 1.98/2.17         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 1.98/2.17      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.98/2.17  thf('149', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.98/2.17      inference('sup-', [status(thm)], ['147', '148'])).
% 1.98/2.17  thf('150', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 1.98/2.17           = (k1_xboole_0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['146', '149'])).
% 1.98/2.17  thf('151', plain,
% 1.98/2.17      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 1.98/2.17      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.98/2.17  thf('152', plain,
% 1.98/2.17      (![X9 : $i, X11 : $i]:
% 1.98/2.17         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 1.98/2.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.98/2.17  thf('153', plain,
% 1.98/2.17      (![X0 : $i, X1 : $i]:
% 1.98/2.17         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.98/2.17          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['151', '152'])).
% 1.98/2.17  thf('154', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         (~ (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 1.98/2.17          | ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 1.98/2.17              = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.98/2.17      inference('sup-', [status(thm)], ['150', '153'])).
% 1.98/2.17  thf('155', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         ((k2_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 1.98/2.17           = (k1_xboole_0))),
% 1.98/2.17      inference('sup+', [status(thm)], ['146', '149'])).
% 1.98/2.17  thf('156', plain,
% 1.98/2.17      (![X0 : $i]:
% 1.98/2.17         (~ (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 1.98/2.17          | ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.98/2.17      inference('demod', [status(thm)], ['154', '155'])).
% 1.98/2.17  thf('157', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.98/2.17      inference('sup-', [status(thm)], ['3', '44'])).
% 1.98/2.17  thf('158', plain,
% 1.98/2.17      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.98/2.17      inference('demod', [status(thm)], ['156', '157'])).
% 1.98/2.17  thf('159', plain,
% 1.98/2.17      ((![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ X0)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup+', [status(thm)], ['145', '158'])).
% 1.98/2.17  thf('160', plain,
% 1.98/2.17      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('simplify', [status(thm)], ['113'])).
% 1.98/2.17  thf('161', plain,
% 1.98/2.17      ((![X0 : $i]: ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ X0)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('demod', [status(thm)], ['159', '160'])).
% 1.98/2.17  thf('162', plain,
% 1.98/2.17      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('sup+', [status(thm)], ['126', '127'])).
% 1.98/2.17  thf('163', plain,
% 1.98/2.17      ((((sk_C_2) = (k1_tarski @ sk_A)))
% 1.98/2.17         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.98/2.17      inference('demod', [status(thm)], ['144', '161', '162'])).
% 1.98/2.17  thf('164', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 1.98/2.17      inference('simpl_trail', [status(thm)], ['106', '118'])).
% 1.98/2.17  thf('165', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('simplify_reflect-', [status(thm)], ['163', '164'])).
% 1.98/2.17  thf('166', plain,
% 1.98/2.17      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.98/2.17      inference('split', [status(esa)], ['111'])).
% 1.98/2.17  thf('167', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 1.98/2.17      inference('sat_resolution*', [status(thm)], ['165', '166'])).
% 1.98/2.17  thf('168', plain, (((sk_B_1) = (k1_xboole_0))),
% 1.98/2.17      inference('simpl_trail', [status(thm)], ['125', '167'])).
% 1.98/2.17  thf('169', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0))),
% 1.98/2.17      inference('demod', [status(thm)], ['47', '168'])).
% 1.98/2.17  thf('170', plain, (((k1_tarski @ sk_A) = (sk_C_2))),
% 1.98/2.17      inference('demod', [status(thm)], ['0', '169'])).
% 1.98/2.17  thf('171', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 1.98/2.17      inference('simpl_trail', [status(thm)], ['106', '118'])).
% 1.98/2.17  thf('172', plain, ($false),
% 1.98/2.17      inference('simplify_reflect-', [status(thm)], ['170', '171'])).
% 1.98/2.17  
% 1.98/2.17  % SZS output end Refutation
% 1.98/2.17  
% 1.98/2.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
