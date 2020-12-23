%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1O1v7gw0Fj

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:29 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  222 (2134 expanded)
%              Number of leaves         :   32 ( 617 expanded)
%              Depth                    :   31
%              Number of atoms          : 1648 (25095 expanded)
%              Number of equality atoms :  264 (5013 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( r2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_xboole_0 @ X17 @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('29',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k3_xboole_0 @ X5 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','33'])).

thf('35',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('38',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','42'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

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

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('46',plain,(
    ! [X58: $i,X59: $i] :
      ( ( X59
        = ( k1_tarski @ X58 ) )
      | ( X59 = k1_xboole_0 )
      | ~ ( r1_tarski @ X59 @ ( k1_tarski @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('55',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('56',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('62',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('73',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('76',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['68'])).

thf('83',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['72','74','84'])).

thf('86',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['71','85'])).

thf('87',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['67','86'])).

thf('88',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['77'])).

thf('89',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( X0 = sk_B_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['67','86'])).

thf('94',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('95',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('97',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = ( k5_xboole_0 @ sk_C_2 @ k1_xboole_0 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('103',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('105',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_2 ) @ X0 )
        = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ sk_C_2 @ ( k5_xboole_0 @ sk_C_2 @ X0 ) ) ) )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_2 ) @ X0 )
        = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_2 ) @ X0 )
        = X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_C_2 ) )
        = X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('117',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ( ( k3_xboole_0 @ X5 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('118',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['67','86'])).

thf('120',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_C_2 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('122',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k5_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('128',plain,
    ( ( ( k5_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('134',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('136',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( X0
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ ( k5_xboole_0 @ X0 @ sk_C_2 ) ) ) )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['138','141','142'])).

thf('144',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','143'])).

thf('145',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C_2 )
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(condensation,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('150',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['148','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['146','153'])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 )
          = sk_C_2 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','154'])).

thf('156',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
          = sk_C_2 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['71','85'])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','159'])).

thf('161',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('162',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('163',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','40'])).

thf('164',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['89'])).

thf('166',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('167',plain,
    ( $false
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['160','161','164','165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','42'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('170',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('171',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['146','153'])).

thf('173',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C_2 )
          = sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('175',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
          = sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['71','85'])).

thf('177',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_C_2 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','177'])).

thf('179',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('180',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('181',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','40'])).

thf('182',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('184',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('185',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['178','179','182','183','184'])).

thf('186',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['77'])).

thf('187',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['185','186'])).

thf('188',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['167','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1O1v7gw0Fj
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:19:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.53/2.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.53/2.77  % Solved by: fo/fo7.sh
% 2.53/2.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.53/2.77  % done 6309 iterations in 2.312s
% 2.53/2.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.53/2.77  % SZS output start Refutation
% 2.53/2.77  thf(sk_A_type, type, sk_A: $i).
% 2.53/2.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.53/2.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.53/2.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.53/2.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.53/2.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.53/2.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.53/2.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.53/2.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.53/2.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.53/2.77  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 2.53/2.77  thf(sk_B_type, type, sk_B: $i > $i).
% 2.53/2.77  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.53/2.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.53/2.77  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.53/2.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.53/2.77  thf(t17_xboole_1, axiom,
% 2.53/2.77    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.53/2.77  thf('0', plain,
% 2.53/2.77      (![X19 : $i, X20 : $i]: (r1_tarski @ (k3_xboole_0 @ X19 @ X20) @ X19)),
% 2.53/2.77      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.53/2.77  thf(d8_xboole_0, axiom,
% 2.53/2.77    (![A:$i,B:$i]:
% 2.53/2.77     ( ( r2_xboole_0 @ A @ B ) <=>
% 2.53/2.77       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 2.53/2.77  thf('1', plain,
% 2.53/2.77      (![X8 : $i, X10 : $i]:
% 2.53/2.77         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 2.53/2.77      inference('cnf', [status(esa)], [d8_xboole_0])).
% 2.53/2.77  thf('2', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         (((k3_xboole_0 @ X0 @ X1) = (X0))
% 2.53/2.77          | (r2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['0', '1'])).
% 2.53/2.77  thf(t6_xboole_0, axiom,
% 2.53/2.77    (![A:$i,B:$i]:
% 2.53/2.77     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 2.53/2.77          ( ![C:$i]:
% 2.53/2.77            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 2.53/2.77  thf('3', plain,
% 2.53/2.77      (![X17 : $i, X18 : $i]:
% 2.53/2.77         (~ (r2_xboole_0 @ X17 @ X18)
% 2.53/2.77          | (r2_hidden @ (sk_C_1 @ X18 @ X17) @ X18))),
% 2.53/2.77      inference('cnf', [status(esa)], [t6_xboole_0])).
% 2.53/2.77  thf('4', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         (((k3_xboole_0 @ X0 @ X1) = (X0))
% 2.53/2.77          | (r2_hidden @ (sk_C_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['2', '3'])).
% 2.53/2.77  thf(idempotence_k2_xboole_0, axiom,
% 2.53/2.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.53/2.77  thf('5', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ X11) = (X11))),
% 2.53/2.77      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.53/2.77  thf(t95_xboole_1, axiom,
% 2.53/2.77    (![A:$i,B:$i]:
% 2.53/2.77     ( ( k3_xboole_0 @ A @ B ) =
% 2.53/2.77       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.53/2.77  thf('6', plain,
% 2.53/2.77      (![X28 : $i, X29 : $i]:
% 2.53/2.77         ((k3_xboole_0 @ X28 @ X29)
% 2.53/2.77           = (k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ 
% 2.53/2.77              (k2_xboole_0 @ X28 @ X29)))),
% 2.53/2.77      inference('cnf', [status(esa)], [t95_xboole_1])).
% 2.53/2.77  thf(t91_xboole_1, axiom,
% 2.53/2.77    (![A:$i,B:$i,C:$i]:
% 2.53/2.77     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.53/2.77       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.53/2.77  thf('7', plain,
% 2.53/2.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 2.53/2.77           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 2.53/2.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.53/2.77  thf('8', plain,
% 2.53/2.77      (![X28 : $i, X29 : $i]:
% 2.53/2.77         ((k3_xboole_0 @ X28 @ X29)
% 2.53/2.77           = (k5_xboole_0 @ X28 @ 
% 2.53/2.77              (k5_xboole_0 @ X29 @ (k2_xboole_0 @ X28 @ X29))))),
% 2.53/2.77      inference('demod', [status(thm)], ['6', '7'])).
% 2.53/2.77  thf(commutativity_k5_xboole_0, axiom,
% 2.53/2.77    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 2.53/2.77  thf('9', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.53/2.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.53/2.77  thf(t5_boole, axiom,
% 2.53/2.77    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.53/2.77  thf('10', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 2.53/2.77      inference('cnf', [status(esa)], [t5_boole])).
% 2.53/2.77  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.53/2.77      inference('sup+', [status(thm)], ['9', '10'])).
% 2.53/2.77  thf('12', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.53/2.77           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['8', '11'])).
% 2.53/2.77  thf(idempotence_k3_xboole_0, axiom,
% 2.53/2.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 2.53/2.77  thf('13', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 2.53/2.77      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.53/2.77  thf(t4_xboole_0, axiom,
% 2.53/2.77    (![A:$i,B:$i]:
% 2.53/2.77     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.53/2.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.53/2.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.53/2.77            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.53/2.77  thf('14', plain,
% 2.53/2.77      (![X13 : $i, X14 : $i]:
% 2.53/2.77         ((r1_xboole_0 @ X13 @ X14)
% 2.53/2.77          | (r2_hidden @ (sk_C @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 2.53/2.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.53/2.77  thf(d1_xboole_0, axiom,
% 2.53/2.77    (![A:$i]:
% 2.53/2.77     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.53/2.77  thf('15', plain,
% 2.53/2.77      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 2.53/2.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.53/2.77  thf('16', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['14', '15'])).
% 2.53/2.77  thf('17', plain,
% 2.53/2.77      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['13', '16'])).
% 2.53/2.77  thf(d7_xboole_0, axiom,
% 2.53/2.77    (![A:$i,B:$i]:
% 2.53/2.77     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.53/2.77       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.53/2.77  thf('18', plain,
% 2.53/2.77      (![X5 : $i, X6 : $i]:
% 2.53/2.77         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 2.53/2.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.53/2.77  thf('19', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (~ (v1_xboole_0 @ X0) | ((k3_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['17', '18'])).
% 2.53/2.77  thf('20', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 2.53/2.77      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.53/2.77  thf('21', plain,
% 2.53/2.77      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['19', '20'])).
% 2.53/2.77  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.53/2.77      inference('sup+', [status(thm)], ['9', '10'])).
% 2.53/2.77  thf('23', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         (((k5_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.77      inference('sup+', [status(thm)], ['21', '22'])).
% 2.53/2.77  thf('24', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))
% 2.53/2.77          | ~ (v1_xboole_0 @ X0))),
% 2.53/2.77      inference('sup+', [status(thm)], ['12', '23'])).
% 2.53/2.77  thf('25', plain,
% 2.53/2.77      (![X13 : $i, X15 : $i, X16 : $i]:
% 2.53/2.77         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 2.53/2.77          | ~ (r1_xboole_0 @ X13 @ X16))),
% 2.53/2.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.53/2.77  thf('26', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         (~ (r2_hidden @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 2.53/2.77          | ~ (v1_xboole_0 @ X0)
% 2.53/2.77          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['24', '25'])).
% 2.53/2.77  thf('27', plain,
% 2.53/2.77      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['19', '20'])).
% 2.53/2.77  thf('28', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 2.53/2.77      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.53/2.77  thf('29', plain,
% 2.53/2.77      (![X5 : $i, X7 : $i]:
% 2.53/2.77         ((r1_xboole_0 @ X5 @ X7) | ((k3_xboole_0 @ X5 @ X7) != (k1_xboole_0)))),
% 2.53/2.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.53/2.77  thf('30', plain,
% 2.53/2.77      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['28', '29'])).
% 2.53/2.77  thf('31', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.53/2.77      inference('simplify', [status(thm)], ['30'])).
% 2.53/2.77  thf('32', plain,
% 2.53/2.77      (![X0 : $i]: ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.77      inference('sup+', [status(thm)], ['27', '31'])).
% 2.53/2.77  thf('33', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         (~ (v1_xboole_0 @ X0)
% 2.53/2.77          | ~ (r2_hidden @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.53/2.77      inference('clc', [status(thm)], ['26', '32'])).
% 2.53/2.77  thf('34', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['5', '33'])).
% 2.53/2.77  thf('35', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.53/2.77      inference('simplify', [status(thm)], ['30'])).
% 2.53/2.77  thf('36', plain,
% 2.53/2.77      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 2.53/2.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.53/2.77  thf('37', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 2.53/2.77      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 2.53/2.77  thf('38', plain,
% 2.53/2.77      (![X13 : $i, X15 : $i, X16 : $i]:
% 2.53/2.77         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 2.53/2.77          | ~ (r1_xboole_0 @ X13 @ X16))),
% 2.53/2.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.53/2.77  thf('39', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['37', '38'])).
% 2.53/2.77  thf('40', plain,
% 2.53/2.77      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['36', '39'])).
% 2.53/2.77  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.77      inference('sup-', [status(thm)], ['35', '40'])).
% 2.53/2.77  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.53/2.77      inference('demod', [status(thm)], ['34', '41'])).
% 2.53/2.77  thf('43', plain,
% 2.53/2.77      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['4', '42'])).
% 2.53/2.77  thf(t7_xboole_1, axiom,
% 2.53/2.77    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.53/2.77  thf('44', plain,
% 2.53/2.77      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 2.53/2.77      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.53/2.77  thf(t43_zfmisc_1, conjecture,
% 2.53/2.77    (![A:$i,B:$i,C:$i]:
% 2.53/2.77     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.53/2.77          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.53/2.77          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.53/2.77          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 2.53/2.77  thf(zf_stmt_0, negated_conjecture,
% 2.53/2.77    (~( ![A:$i,B:$i,C:$i]:
% 2.53/2.77        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 2.53/2.77             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.53/2.77             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 2.53/2.77             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 2.53/2.77    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 2.53/2.77  thf('45', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.77  thf(l3_zfmisc_1, axiom,
% 2.53/2.77    (![A:$i,B:$i]:
% 2.53/2.77     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 2.53/2.77       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 2.53/2.77  thf('46', plain,
% 2.53/2.77      (![X58 : $i, X59 : $i]:
% 2.53/2.77         (((X59) = (k1_tarski @ X58))
% 2.53/2.77          | ((X59) = (k1_xboole_0))
% 2.53/2.77          | ~ (r1_tarski @ X59 @ (k1_tarski @ X58)))),
% 2.53/2.77      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 2.53/2.77  thf('47', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77          | ((X0) = (k1_xboole_0))
% 2.53/2.77          | ((X0) = (k1_tarski @ sk_A)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['45', '46'])).
% 2.53/2.77  thf('48', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.77  thf('49', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77          | ((X0) = (k1_xboole_0))
% 2.53/2.77          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 2.53/2.77      inference('demod', [status(thm)], ['47', '48'])).
% 2.53/2.77  thf('50', plain,
% 2.53/2.77      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['44', '49'])).
% 2.53/2.77  thf('51', plain,
% 2.53/2.77      (![X28 : $i, X29 : $i]:
% 2.53/2.77         ((k3_xboole_0 @ X28 @ X29)
% 2.53/2.77           = (k5_xboole_0 @ X28 @ 
% 2.53/2.77              (k5_xboole_0 @ X29 @ (k2_xboole_0 @ X28 @ X29))))),
% 2.53/2.77      inference('demod', [status(thm)], ['6', '7'])).
% 2.53/2.77  thf('52', plain,
% 2.53/2.77      ((((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 2.53/2.77          = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ sk_B_1)))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['50', '51'])).
% 2.53/2.77  thf('53', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.53/2.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.53/2.77  thf('54', plain,
% 2.53/2.77      ((((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 2.53/2.77          = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_C_2)))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['52', '53'])).
% 2.53/2.77  thf(t92_xboole_1, axiom,
% 2.53/2.77    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.53/2.77  thf('55', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ X27) = (k1_xboole_0))),
% 2.53/2.77      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.53/2.77  thf('56', plain,
% 2.53/2.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 2.53/2.77           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 2.53/2.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.53/2.77  thf('57', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.53/2.77           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['55', '56'])).
% 2.53/2.77  thf('58', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.53/2.77      inference('sup+', [status(thm)], ['9', '10'])).
% 2.53/2.77  thf('59', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['57', '58'])).
% 2.53/2.77  thf('60', plain,
% 2.53/2.77      ((((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['54', '59'])).
% 2.53/2.77  thf('61', plain,
% 2.53/2.77      (![X19 : $i, X20 : $i]: (r1_tarski @ (k3_xboole_0 @ X19 @ X20) @ X19)),
% 2.53/2.77      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.53/2.77  thf('62', plain,
% 2.53/2.77      (((r1_tarski @ sk_C_2 @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['60', '61'])).
% 2.53/2.77  thf('63', plain,
% 2.53/2.77      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['44', '49'])).
% 2.53/2.77  thf('64', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77          | ((X0) = (k1_xboole_0))
% 2.53/2.77          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 2.53/2.77      inference('demod', [status(thm)], ['47', '48'])).
% 2.53/2.77  thf('65', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (~ (r1_tarski @ X0 @ sk_B_1)
% 2.53/2.77          | ((sk_B_1) = (k1_xboole_0))
% 2.53/2.77          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77          | ((X0) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['63', '64'])).
% 2.53/2.77  thf('66', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))
% 2.53/2.77        | ((sk_C_2) = (k1_xboole_0))
% 2.53/2.77        | ((sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['62', '65'])).
% 2.53/2.77  thf('67', plain,
% 2.53/2.77      ((((sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77        | ((sk_C_2) = (k1_xboole_0))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('simplify', [status(thm)], ['66'])).
% 2.53/2.77  thf('68', plain,
% 2.53/2.77      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 2.53/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.77  thf('69', plain,
% 2.53/2.77      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 2.53/2.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('split', [status(esa)], ['68'])).
% 2.53/2.77  thf('70', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.77  thf('71', plain,
% 2.53/2.77      ((((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 2.53/2.77         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('demod', [status(thm)], ['69', '70'])).
% 2.53/2.77  thf('72', plain,
% 2.53/2.77      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('split', [status(esa)], ['68'])).
% 2.53/2.77  thf('73', plain,
% 2.53/2.77      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 2.53/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.77  thf('74', plain,
% 2.53/2.77      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 2.53/2.77       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.53/2.77      inference('split', [status(esa)], ['73'])).
% 2.53/2.77  thf('75', plain,
% 2.53/2.77      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['44', '49'])).
% 2.53/2.77  thf('76', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.77  thf('77', plain,
% 2.53/2.77      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 2.53/2.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.53/2.77  thf('78', plain,
% 2.53/2.77      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('split', [status(esa)], ['77'])).
% 2.53/2.77  thf('79', plain,
% 2.53/2.77      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('sup-', [status(thm)], ['76', '78'])).
% 2.53/2.77  thf('80', plain,
% 2.53/2.77      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('sup-', [status(thm)], ['75', '79'])).
% 2.53/2.77  thf('81', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['80'])).
% 2.53/2.77  thf('82', plain,
% 2.53/2.77      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 2.53/2.77      inference('split', [status(esa)], ['68'])).
% 2.53/2.77  thf('83', plain,
% 2.53/2.77      ((((sk_B_1) != (sk_B_1)))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 2.53/2.77             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('sup-', [status(thm)], ['81', '82'])).
% 2.53/2.77  thf('84', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.53/2.77      inference('simplify', [status(thm)], ['83'])).
% 2.53/2.77  thf('85', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 2.53/2.77      inference('sat_resolution*', [status(thm)], ['72', '74', '84'])).
% 2.53/2.77  thf('86', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('simpl_trail', [status(thm)], ['71', '85'])).
% 2.53/2.77  thf('87', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('simplify_reflect-', [status(thm)], ['67', '86'])).
% 2.53/2.77  thf('88', plain,
% 2.53/2.77      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('split', [status(esa)], ['77'])).
% 2.53/2.77  thf('89', plain,
% 2.53/2.77      (((((sk_C_2) != (sk_C_2)) | ((sk_B_1) = (k1_xboole_0))))
% 2.53/2.77         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('sup-', [status(thm)], ['87', '88'])).
% 2.53/2.77  thf('90', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['89'])).
% 2.53/2.77  thf('91', plain,
% 2.53/2.77      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['19', '20'])).
% 2.53/2.77  thf('92', plain,
% 2.53/2.77      ((![X0 : $i]: (((X0) = (sk_B_1)) | ~ (v1_xboole_0 @ X0)))
% 2.53/2.77         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('sup+', [status(thm)], ['90', '91'])).
% 2.53/2.77  thf('93', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('simplify_reflect-', [status(thm)], ['67', '86'])).
% 2.53/2.77  thf('94', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.53/2.77      inference('simplify', [status(thm)], ['30'])).
% 2.53/2.77  thf('95', plain,
% 2.53/2.77      (((r1_xboole_0 @ k1_xboole_0 @ sk_C_2) | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['93', '94'])).
% 2.53/2.77  thf('96', plain,
% 2.53/2.77      (![X5 : $i, X6 : $i]:
% 2.53/2.77         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 2.53/2.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.53/2.77  thf('97', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))
% 2.53/2.77        | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_2) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['95', '96'])).
% 2.53/2.77  thf('98', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.53/2.77           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['8', '11'])).
% 2.53/2.77  thf('99', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['57', '58'])).
% 2.53/2.77  thf('100', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 2.53/2.77           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['98', '99'])).
% 2.53/2.77  thf('101', plain,
% 2.53/2.77      ((((k2_xboole_0 @ k1_xboole_0 @ sk_C_2)
% 2.53/2.77          = (k5_xboole_0 @ sk_C_2 @ k1_xboole_0))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['97', '100'])).
% 2.53/2.77  thf('102', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 2.53/2.77      inference('cnf', [status(esa)], [t5_boole])).
% 2.53/2.77  thf('103', plain,
% 2.53/2.77      ((((k2_xboole_0 @ k1_xboole_0 @ sk_C_2) = (sk_C_2))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['101', '102'])).
% 2.53/2.77  thf('104', plain,
% 2.53/2.77      (![X28 : $i, X29 : $i]:
% 2.53/2.77         ((k3_xboole_0 @ X28 @ X29)
% 2.53/2.77           = (k5_xboole_0 @ X28 @ 
% 2.53/2.77              (k5_xboole_0 @ X29 @ (k2_xboole_0 @ X28 @ X29))))),
% 2.53/2.77      inference('demod', [status(thm)], ['6', '7'])).
% 2.53/2.77  thf('105', plain,
% 2.53/2.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 2.53/2.77           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 2.53/2.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.53/2.77  thf('106', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.53/2.77           = (k5_xboole_0 @ X1 @ 
% 2.53/2.77              (k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['104', '105'])).
% 2.53/2.77  thf('107', plain,
% 2.53/2.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 2.53/2.77           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 2.53/2.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.53/2.77  thf('108', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.53/2.77           = (k5_xboole_0 @ X1 @ 
% 2.53/2.77              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 2.53/2.77      inference('demod', [status(thm)], ['106', '107'])).
% 2.53/2.77  thf('109', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_2) @ X0)
% 2.53/2.77            = (k5_xboole_0 @ k1_xboole_0 @ 
% 2.53/2.77               (k5_xboole_0 @ sk_C_2 @ (k5_xboole_0 @ sk_C_2 @ X0))))
% 2.53/2.77          | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['103', '108'])).
% 2.53/2.77  thf('110', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['57', '58'])).
% 2.53/2.77  thf('111', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_2) @ X0)
% 2.53/2.77            = (k5_xboole_0 @ k1_xboole_0 @ X0))
% 2.53/2.77          | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['109', '110'])).
% 2.53/2.77  thf('112', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.53/2.77      inference('sup+', [status(thm)], ['9', '10'])).
% 2.53/2.77  thf('113', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (((k5_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_2) @ X0) = (X0))
% 2.53/2.77          | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['111', '112'])).
% 2.53/2.77  thf('114', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.53/2.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.53/2.77  thf('115', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (((k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_C_2)) = (X0))
% 2.53/2.77          | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['113', '114'])).
% 2.53/2.77  thf('116', plain,
% 2.53/2.77      ((((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['54', '59'])).
% 2.53/2.77  thf('117', plain,
% 2.53/2.77      (![X5 : $i, X7 : $i]:
% 2.53/2.77         ((r1_xboole_0 @ X5 @ X7) | ((k3_xboole_0 @ X5 @ X7) != (k1_xboole_0)))),
% 2.53/2.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.53/2.77  thf('118', plain,
% 2.53/2.77      ((((sk_C_2) != (k1_xboole_0))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0))
% 2.53/2.77        | (r1_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('sup-', [status(thm)], ['116', '117'])).
% 2.53/2.77  thf('119', plain,
% 2.53/2.77      ((((sk_C_2) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('simplify_reflect-', [status(thm)], ['67', '86'])).
% 2.53/2.77  thf('120', plain,
% 2.53/2.77      (((r1_xboole_0 @ sk_B_1 @ sk_C_2) | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('clc', [status(thm)], ['118', '119'])).
% 2.53/2.77  thf('121', plain,
% 2.53/2.77      (![X5 : $i, X6 : $i]:
% 2.53/2.77         (((k3_xboole_0 @ X5 @ X6) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 2.53/2.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.53/2.77  thf('122', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))
% 2.53/2.77        | ((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['120', '121'])).
% 2.53/2.77  thf('123', plain,
% 2.53/2.77      (![X28 : $i, X29 : $i]:
% 2.53/2.77         ((k3_xboole_0 @ X28 @ X29)
% 2.53/2.77           = (k5_xboole_0 @ X28 @ 
% 2.53/2.77              (k5_xboole_0 @ X29 @ (k2_xboole_0 @ X28 @ X29))))),
% 2.53/2.77      inference('demod', [status(thm)], ['6', '7'])).
% 2.53/2.77  thf('124', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['57', '58'])).
% 2.53/2.77  thf('125', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 2.53/2.77           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['123', '124'])).
% 2.53/2.77  thf('126', plain,
% 2.53/2.77      ((((k5_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77          = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['122', '125'])).
% 2.53/2.77  thf('127', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 2.53/2.77      inference('cnf', [status(esa)], [t5_boole])).
% 2.53/2.77  thf('128', plain,
% 2.53/2.77      ((((k5_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2)) = (sk_B_1))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['126', '127'])).
% 2.53/2.77  thf('129', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.53/2.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.53/2.77  thf('130', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['57', '58'])).
% 2.53/2.77  thf('131', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['129', '130'])).
% 2.53/2.77  thf('132', plain,
% 2.53/2.77      ((((sk_C_2) = (k5_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ sk_B_1))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['128', '131'])).
% 2.53/2.77  thf('133', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.53/2.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.53/2.77  thf('134', plain,
% 2.53/2.77      ((((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['132', '133'])).
% 2.53/2.77  thf('135', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['129', '130'])).
% 2.53/2.77  thf('136', plain,
% 2.53/2.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 2.53/2.77           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 2.53/2.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.53/2.77  thf('137', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.77         ((X0)
% 2.53/2.77           = (k5_xboole_0 @ X2 @ 
% 2.53/2.77              (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1)))))),
% 2.53/2.77      inference('sup+', [status(thm)], ['135', '136'])).
% 2.53/2.77  thf('138', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (((X0)
% 2.53/2.77            = (k5_xboole_0 @ sk_B_1 @ 
% 2.53/2.77               (k5_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ 
% 2.53/2.77                (k5_xboole_0 @ X0 @ sk_C_2))))
% 2.53/2.77          | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['134', '137'])).
% 2.53/2.77  thf('139', plain,
% 2.53/2.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 2.53/2.77           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 2.53/2.77      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.53/2.77  thf('140', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.53/2.77      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.53/2.77  thf('141', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 2.53/2.77           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['139', '140'])).
% 2.53/2.77  thf('142', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.53/2.77         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.53/2.77           = (k5_xboole_0 @ X1 @ 
% 2.53/2.77              (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 2.53/2.77      inference('demod', [status(thm)], ['106', '107'])).
% 2.53/2.77  thf('143', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (((X0) = (k5_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_2) @ X0))
% 2.53/2.77          | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['138', '141', '142'])).
% 2.53/2.77  thf('144', plain,
% 2.53/2.77      ((((k3_xboole_0 @ k1_xboole_0 @ sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0))
% 2.53/2.77        | ((sk_B_1) = (k1_xboole_0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['115', '143'])).
% 2.53/2.77  thf('145', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))
% 2.53/2.77        | ((k3_xboole_0 @ k1_xboole_0 @ sk_C_2)
% 2.53/2.77            = (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 2.53/2.77      inference('simplify', [status(thm)], ['144'])).
% 2.53/2.77  thf('146', plain,
% 2.53/2.77      (((k3_xboole_0 @ k1_xboole_0 @ sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('condensation', [status(thm)], ['145'])).
% 2.53/2.77  thf('147', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.53/2.77           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['8', '11'])).
% 2.53/2.77  thf('148', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['57', '58'])).
% 2.53/2.77  thf('149', plain,
% 2.53/2.77      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['19', '20'])).
% 2.53/2.77  thf('150', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 2.53/2.77      inference('cnf', [status(esa)], [t5_boole])).
% 2.53/2.77  thf('151', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 2.53/2.77      inference('sup+', [status(thm)], ['149', '150'])).
% 2.53/2.77  thf('152', plain,
% 2.53/2.77      (![X0 : $i, X1 : $i]:
% 2.53/2.77         (((X0) = (X1)) | ~ (v1_xboole_0 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.53/2.77      inference('sup+', [status(thm)], ['148', '151'])).
% 2.53/2.77  thf('153', plain,
% 2.53/2.77      (![X0 : $i]:
% 2.53/2.77         (~ (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 2.53/2.77          | ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['147', '152'])).
% 2.53/2.77  thf('154', plain,
% 2.53/2.77      ((~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77        | ((k2_xboole_0 @ k1_xboole_0 @ sk_C_2) = (sk_C_2)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['146', '153'])).
% 2.53/2.77  thf('155', plain,
% 2.53/2.77      ((![X0 : $i]:
% 2.53/2.77          (~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2))
% 2.53/2.77           | ~ (v1_xboole_0 @ X0)
% 2.53/2.77           | ((k2_xboole_0 @ k1_xboole_0 @ sk_C_2) = (sk_C_2))))
% 2.53/2.77         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('sup-', [status(thm)], ['92', '154'])).
% 2.53/2.77  thf('156', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['89'])).
% 2.53/2.77  thf('157', plain,
% 2.53/2.77      ((![X0 : $i]:
% 2.53/2.77          (~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2))
% 2.53/2.77           | ~ (v1_xboole_0 @ X0)
% 2.53/2.77           | ((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))))
% 2.53/2.77         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('demod', [status(thm)], ['155', '156'])).
% 2.53/2.77  thf('158', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('simpl_trail', [status(thm)], ['71', '85'])).
% 2.53/2.77  thf('159', plain,
% 2.53/2.77      ((![X0 : $i]:
% 2.53/2.77          (~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2)) | ~ (v1_xboole_0 @ X0)))
% 2.53/2.77         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('simplify_reflect-', [status(thm)], ['157', '158'])).
% 2.53/2.77  thf('160', plain,
% 2.53/2.77      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 2.53/2.77         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('sup-', [status(thm)], ['43', '159'])).
% 2.53/2.77  thf('161', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['89'])).
% 2.53/2.77  thf('162', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['89'])).
% 2.53/2.77  thf('163', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.77      inference('sup-', [status(thm)], ['35', '40'])).
% 2.53/2.77  thf('164', plain,
% 2.53/2.77      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('sup+', [status(thm)], ['162', '163'])).
% 2.53/2.77  thf('165', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['89'])).
% 2.53/2.77  thf('166', plain,
% 2.53/2.77      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('sup+', [status(thm)], ['162', '163'])).
% 2.53/2.77  thf('167', plain, (($false) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 2.53/2.77      inference('demod', [status(thm)], ['160', '161', '164', '165', '166'])).
% 2.53/2.77  thf('168', plain,
% 2.53/2.77      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.53/2.77      inference('sup-', [status(thm)], ['4', '42'])).
% 2.53/2.77  thf('169', plain,
% 2.53/2.77      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.53/2.77      inference('demod', [status(thm)], ['19', '20'])).
% 2.53/2.77  thf('170', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['80'])).
% 2.53/2.77  thf('171', plain,
% 2.53/2.77      ((![X0 : $i]: (((sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('sup+', [status(thm)], ['169', '170'])).
% 2.53/2.77  thf('172', plain,
% 2.53/2.77      ((~ (v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 2.53/2.77        | ((k2_xboole_0 @ k1_xboole_0 @ sk_C_2) = (sk_C_2)))),
% 2.53/2.77      inference('sup-', [status(thm)], ['146', '153'])).
% 2.53/2.77  thf('173', plain,
% 2.53/2.77      ((![X0 : $i]:
% 2.53/2.77          (~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2))
% 2.53/2.77           | ~ (v1_xboole_0 @ X0)
% 2.53/2.77           | ((k2_xboole_0 @ k1_xboole_0 @ sk_C_2) = (sk_C_2))))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('sup-', [status(thm)], ['171', '172'])).
% 2.53/2.77  thf('174', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['80'])).
% 2.53/2.77  thf('175', plain,
% 2.53/2.77      ((![X0 : $i]:
% 2.53/2.77          (~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2))
% 2.53/2.77           | ~ (v1_xboole_0 @ X0)
% 2.53/2.77           | ((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('demod', [status(thm)], ['173', '174'])).
% 2.53/2.77  thf('176', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 2.53/2.77      inference('simpl_trail', [status(thm)], ['71', '85'])).
% 2.53/2.77  thf('177', plain,
% 2.53/2.77      ((![X0 : $i]:
% 2.53/2.77          (~ (v1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_C_2)) | ~ (v1_xboole_0 @ X0)))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('simplify_reflect-', [status(thm)], ['175', '176'])).
% 2.53/2.77  thf('178', plain,
% 2.53/2.77      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 2.53/2.77         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('sup-', [status(thm)], ['168', '177'])).
% 2.53/2.77  thf('179', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['80'])).
% 2.53/2.77  thf('180', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['80'])).
% 2.53/2.77  thf('181', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.53/2.77      inference('sup-', [status(thm)], ['35', '40'])).
% 2.53/2.77  thf('182', plain,
% 2.53/2.77      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('sup+', [status(thm)], ['180', '181'])).
% 2.53/2.77  thf('183', plain,
% 2.53/2.77      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('simplify', [status(thm)], ['80'])).
% 2.53/2.77  thf('184', plain,
% 2.53/2.77      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 2.53/2.77      inference('sup+', [status(thm)], ['180', '181'])).
% 2.53/2.77  thf('185', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.53/2.77      inference('demod', [status(thm)], ['178', '179', '182', '183', '184'])).
% 2.53/2.77  thf('186', plain,
% 2.53/2.77      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 2.53/2.77      inference('split', [status(esa)], ['77'])).
% 2.53/2.77  thf('187', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 2.53/2.77      inference('sat_resolution*', [status(thm)], ['185', '186'])).
% 2.53/2.77  thf('188', plain, ($false),
% 2.53/2.77      inference('simpl_trail', [status(thm)], ['167', '187'])).
% 2.53/2.77  
% 2.53/2.77  % SZS output end Refutation
% 2.53/2.77  
% 2.53/2.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
