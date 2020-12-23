%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LRKUM7VXzx

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:40 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 725 expanded)
%              Number of leaves         :   31 ( 233 expanded)
%              Depth                    :   19
%              Number of atoms          :  886 (5263 expanded)
%              Number of equality atoms :   75 ( 530 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['2'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('18',plain,(
    sk_C_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_C_3 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_C_3 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('27',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ( X34 = X31 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('28',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34 = X31 )
      | ~ ( r2_hidden @ X34 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('32',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('39',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 )
      | ( ( sk_C @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('48',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_3 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['46','49'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('53',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_3 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_3 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('56',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('59',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('63',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','66'])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_3 )
    = sk_C_3 ),
    inference(demod,[status(thm)],['54','55','67'])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('71',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
      | ( ( sk_B @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('77',plain,(
    ! [X64: $i,X66: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X64 ) @ X66 )
      | ~ ( r2_hidden @ X64 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('84',plain,(
    ! [X18: $i,X20: $i] :
      ( ( X18 = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
      | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_3 )
        = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ( r2_hidden @ ( sk_C_1 @ X15 @ X14 ) @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('88',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_3 )
        = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_3 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('92',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_3 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('93',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_3 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['46','49'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( k3_xboole_0 @ sk_B_1 @ X0 ) )
      | ( r1_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( sk_B_1 = sk_C_3 )
    | ( r1_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['68','94'])).

thf('96',plain,(
    sk_B_1 != sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_3 ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('99',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_3 )
    = sk_C_3 ),
    inference(demod,[status(thm)],['54','55','67'])).

thf('103',plain,(
    v1_xboole_0 @ sk_C_3 ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['20','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LRKUM7VXzx
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:19:50 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.90/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.17  % Solved by: fo/fo7.sh
% 0.90/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.17  % done 1302 iterations in 0.718s
% 0.90/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.17  % SZS output start Refutation
% 0.90/1.17  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.17  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.90/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.17  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.17  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.90/1.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.17  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.17  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.17  thf(idempotence_k3_xboole_0, axiom,
% 0.90/1.17    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.90/1.17  thf('0', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 0.90/1.17      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.17  thf(d7_xboole_0, axiom,
% 0.90/1.17    (![A:$i,B:$i]:
% 0.90/1.17     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.90/1.17       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.17  thf('1', plain,
% 0.90/1.17      (![X9 : $i, X11 : $i]:
% 0.90/1.17         ((r1_xboole_0 @ X9 @ X11)
% 0.90/1.17          | ((k3_xboole_0 @ X9 @ X11) != (k1_xboole_0)))),
% 0.90/1.17      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.90/1.17  thf('2', plain,
% 0.90/1.17      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.17  thf('3', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.90/1.17      inference('simplify', [status(thm)], ['2'])).
% 0.90/1.17  thf(d1_xboole_0, axiom,
% 0.90/1.17    (![A:$i]:
% 0.90/1.17     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.90/1.17  thf('4', plain,
% 0.90/1.17      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.17  thf('5', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 0.90/1.17      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.17  thf(t4_xboole_0, axiom,
% 0.90/1.17    (![A:$i,B:$i]:
% 0.90/1.17     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.17            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.17       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.17            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.17  thf('6', plain,
% 0.90/1.17      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 0.90/1.17          | ~ (r1_xboole_0 @ X14 @ X17))),
% 0.90/1.17      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.90/1.17  thf('7', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.17  thf('8', plain,
% 0.90/1.17      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['4', '7'])).
% 0.90/1.17  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.17      inference('sup-', [status(thm)], ['3', '8'])).
% 0.90/1.17  thf(d3_tarski, axiom,
% 0.90/1.17    (![A:$i,B:$i]:
% 0.90/1.17     ( ( r1_tarski @ A @ B ) <=>
% 0.90/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.90/1.17  thf('10', plain,
% 0.90/1.17      (![X6 : $i, X8 : $i]:
% 0.90/1.17         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.90/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.17  thf('11', plain,
% 0.90/1.17      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.17  thf('12', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.17  thf('13', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.17  thf(d10_xboole_0, axiom,
% 0.90/1.17    (![A:$i,B:$i]:
% 0.90/1.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.17  thf('14', plain,
% 0.90/1.17      (![X18 : $i, X20 : $i]:
% 0.90/1.17         (((X18) = (X20))
% 0.90/1.17          | ~ (r1_tarski @ X20 @ X18)
% 0.90/1.17          | ~ (r1_tarski @ X18 @ X20))),
% 0.90/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.17  thf('15', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.17  thf('16', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['12', '15'])).
% 0.90/1.17  thf('17', plain,
% 0.90/1.17      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['9', '16'])).
% 0.90/1.17  thf(t44_zfmisc_1, conjecture,
% 0.90/1.17    (![A:$i,B:$i,C:$i]:
% 0.90/1.17     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.90/1.17          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.17          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.90/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.17        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.90/1.17             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.17             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.90/1.17    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.90/1.17  thf('18', plain, (((sk_C_3) != (k1_xboole_0))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('19', plain, (![X0 : $i]: (((sk_C_3) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.17  thf('20', plain, (~ (v1_xboole_0 @ sk_C_3)),
% 0.90/1.17      inference('simplify', [status(thm)], ['19'])).
% 0.90/1.17  thf('21', plain,
% 0.90/1.17      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.17  thf(t7_xboole_1, axiom,
% 0.90/1.17    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.17  thf('22', plain,
% 0.90/1.17      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 0.90/1.17      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.17  thf('23', plain,
% 0.90/1.17      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X5 @ X6)
% 0.90/1.17          | (r2_hidden @ X5 @ X7)
% 0.90/1.17          | ~ (r1_tarski @ X6 @ X7))),
% 0.90/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.17  thf('24', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.17         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.90/1.17      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.17  thf('25', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         ((v1_xboole_0 @ X0)
% 0.90/1.17          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['21', '24'])).
% 0.90/1.17  thf('26', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf(d1_tarski, axiom,
% 0.90/1.17    (![A:$i,B:$i]:
% 0.90/1.17     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.90/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.90/1.17  thf('27', plain,
% 0.90/1.17      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X34 @ X33)
% 0.90/1.17          | ((X34) = (X31))
% 0.90/1.17          | ((X33) != (k1_tarski @ X31)))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_tarski])).
% 0.90/1.17  thf('28', plain,
% 0.90/1.17      (![X31 : $i, X34 : $i]:
% 0.90/1.17         (((X34) = (X31)) | ~ (r2_hidden @ X34 @ (k1_tarski @ X31)))),
% 0.90/1.17      inference('simplify', [status(thm)], ['27'])).
% 0.90/1.17  thf('29', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3))
% 0.90/1.17          | ((X0) = (sk_A)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['26', '28'])).
% 0.90/1.17  thf('30', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_B @ sk_B_1) = (sk_A)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['25', '29'])).
% 0.90/1.17  thf('31', plain,
% 0.90/1.17      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['9', '16'])).
% 0.90/1.17  thf('32', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('33', plain, (![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.17  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.17      inference('simplify', [status(thm)], ['33'])).
% 0.90/1.17  thf('35', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.90/1.17      inference('clc', [status(thm)], ['30', '34'])).
% 0.90/1.17  thf('36', plain,
% 0.90/1.17      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.17  thf('37', plain, (((r2_hidden @ sk_A @ sk_B_1) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.17      inference('sup+', [status(thm)], ['35', '36'])).
% 0.90/1.17  thf('38', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.17      inference('simplify', [status(thm)], ['33'])).
% 0.90/1.17  thf('39', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.90/1.17      inference('clc', [status(thm)], ['37', '38'])).
% 0.90/1.17  thf('40', plain,
% 0.90/1.17      (![X6 : $i, X8 : $i]:
% 0.90/1.17         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.90/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.17  thf('41', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3))
% 0.90/1.17          | ((X0) = (sk_A)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['26', '28'])).
% 0.90/1.17  thf('42', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0)
% 0.90/1.17          | ((sk_C @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3)) = (sk_A)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.17  thf('43', plain,
% 0.90/1.17      (![X6 : $i, X8 : $i]:
% 0.90/1.17         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 0.90/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.17  thf('44', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (~ (r2_hidden @ sk_A @ X0)
% 0.90/1.17          | (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0)
% 0.90/1.17          | (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['42', '43'])).
% 0.90/1.17  thf('45', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0)
% 0.90/1.17          | ~ (r2_hidden @ sk_A @ X0))),
% 0.90/1.17      inference('simplify', [status(thm)], ['44'])).
% 0.90/1.17  thf('46', plain, ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ sk_B_1)),
% 0.90/1.17      inference('sup-', [status(thm)], ['39', '45'])).
% 0.90/1.17  thf('47', plain,
% 0.90/1.17      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 0.90/1.17      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.17  thf('48', plain,
% 0.90/1.17      (![X18 : $i, X20 : $i]:
% 0.90/1.17         (((X18) = (X20))
% 0.90/1.17          | ~ (r1_tarski @ X20 @ X18)
% 0.90/1.17          | ~ (r1_tarski @ X18 @ X20))),
% 0.90/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.17  thf('49', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.90/1.17          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.17  thf('50', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_3) = (sk_B_1))),
% 0.90/1.17      inference('sup-', [status(thm)], ['46', '49'])).
% 0.90/1.17  thf(t95_xboole_1, axiom,
% 0.90/1.17    (![A:$i,B:$i]:
% 0.90/1.17     ( ( k3_xboole_0 @ A @ B ) =
% 0.90/1.17       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.90/1.17  thf('51', plain,
% 0.90/1.17      (![X29 : $i, X30 : $i]:
% 0.90/1.17         ((k3_xboole_0 @ X29 @ X30)
% 0.90/1.17           = (k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 0.90/1.17              (k2_xboole_0 @ X29 @ X30)))),
% 0.90/1.17      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.90/1.17  thf(t91_xboole_1, axiom,
% 0.90/1.17    (![A:$i,B:$i,C:$i]:
% 0.90/1.17     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.17       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.90/1.17  thf('52', plain,
% 0.90/1.17      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 0.90/1.17           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 0.90/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.17  thf('53', plain,
% 0.90/1.17      (![X29 : $i, X30 : $i]:
% 0.90/1.17         ((k3_xboole_0 @ X29 @ X30)
% 0.90/1.17           = (k5_xboole_0 @ X29 @ 
% 0.90/1.17              (k5_xboole_0 @ X30 @ (k2_xboole_0 @ X29 @ X30))))),
% 0.90/1.17      inference('demod', [status(thm)], ['51', '52'])).
% 0.90/1.17  thf('54', plain,
% 0.90/1.17      (((k3_xboole_0 @ sk_B_1 @ sk_C_3)
% 0.90/1.17         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_3 @ sk_B_1)))),
% 0.90/1.17      inference('sup+', [status(thm)], ['50', '53'])).
% 0.90/1.17  thf(commutativity_k5_xboole_0, axiom,
% 0.90/1.17    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.90/1.17  thf('55', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.90/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.17  thf(t92_xboole_1, axiom,
% 0.90/1.17    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.90/1.17  thf('56', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 0.90/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.90/1.17  thf('57', plain,
% 0.90/1.17      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.17         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 0.90/1.17           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 0.90/1.17      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.90/1.17  thf('58', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.17           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.17      inference('sup+', [status(thm)], ['56', '57'])).
% 0.90/1.17  thf(idempotence_k2_xboole_0, axiom,
% 0.90/1.17    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.90/1.17  thf('59', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ X12) = (X12))),
% 0.90/1.17      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.90/1.17  thf('60', plain,
% 0.90/1.17      (![X29 : $i, X30 : $i]:
% 0.90/1.17         ((k3_xboole_0 @ X29 @ X30)
% 0.90/1.17           = (k5_xboole_0 @ X29 @ 
% 0.90/1.17              (k5_xboole_0 @ X30 @ (k2_xboole_0 @ X29 @ X30))))),
% 0.90/1.17      inference('demod', [status(thm)], ['51', '52'])).
% 0.90/1.17  thf('61', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((k3_xboole_0 @ X0 @ X0)
% 0.90/1.17           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.90/1.17      inference('sup+', [status(thm)], ['59', '60'])).
% 0.90/1.17  thf('62', plain, (![X13 : $i]: ((k3_xboole_0 @ X13 @ X13) = (X13))),
% 0.90/1.17      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.90/1.17  thf('63', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 0.90/1.17      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.90/1.17  thf('64', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.17      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.90/1.17  thf('65', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.90/1.17      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.90/1.17  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.90/1.17      inference('sup+', [status(thm)], ['64', '65'])).
% 0.90/1.17  thf('67', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.90/1.17      inference('demod', [status(thm)], ['58', '66'])).
% 0.90/1.17  thf('68', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_3) = (sk_C_3))),
% 0.90/1.17      inference('demod', [status(thm)], ['54', '55', '67'])).
% 0.90/1.17  thf('69', plain,
% 0.90/1.17      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.17  thf(t17_xboole_1, axiom,
% 0.90/1.17    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.17  thf('70', plain,
% 0.90/1.17      (![X21 : $i, X22 : $i]: (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ X21)),
% 0.90/1.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.17  thf('71', plain,
% 0.90/1.17      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X5 @ X6)
% 0.90/1.17          | (r2_hidden @ X5 @ X7)
% 0.90/1.17          | ~ (r1_tarski @ X6 @ X7))),
% 0.90/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.90/1.17  thf('72', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.17         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['70', '71'])).
% 0.90/1.17  thf('73', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.90/1.17          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.90/1.17      inference('sup-', [status(thm)], ['69', '72'])).
% 0.90/1.17  thf('74', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3))
% 0.90/1.17          | ((X0) = (sk_A)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['26', '28'])).
% 0.90/1.17  thf('75', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((v1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17          | ((sk_B @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17              = (sk_A)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['73', '74'])).
% 0.90/1.17  thf('76', plain,
% 0.90/1.17      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.17  thf(l1_zfmisc_1, axiom,
% 0.90/1.17    (![A:$i,B:$i]:
% 0.90/1.17     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.90/1.17  thf('77', plain,
% 0.90/1.17      (![X64 : $i, X66 : $i]:
% 0.90/1.17         ((r1_tarski @ (k1_tarski @ X64) @ X66) | ~ (r2_hidden @ X64 @ X66))),
% 0.90/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.90/1.17  thf('78', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['76', '77'])).
% 0.90/1.17  thf('79', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.90/1.17           (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17          | (v1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17          | (v1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0)))),
% 0.90/1.17      inference('sup+', [status(thm)], ['75', '78'])).
% 0.90/1.17  thf('80', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('81', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ 
% 0.90/1.17           (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17          | (v1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17          | (v1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0)))),
% 0.90/1.17      inference('demod', [status(thm)], ['79', '80'])).
% 0.90/1.17  thf('82', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((v1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17          | (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ 
% 0.90/1.17             (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0)))),
% 0.90/1.17      inference('simplify', [status(thm)], ['81'])).
% 0.90/1.17  thf('83', plain,
% 0.90/1.17      (![X21 : $i, X22 : $i]: (r1_tarski @ (k3_xboole_0 @ X21 @ X22) @ X21)),
% 0.90/1.17      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.17  thf('84', plain,
% 0.90/1.17      (![X18 : $i, X20 : $i]:
% 0.90/1.17         (((X18) = (X20))
% 0.90/1.17          | ~ (r1_tarski @ X20 @ X18)
% 0.90/1.17          | ~ (r1_tarski @ X18 @ X20))),
% 0.90/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.17  thf('85', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.90/1.17          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['83', '84'])).
% 0.90/1.17  thf('86', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         ((v1_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17          | ((k2_xboole_0 @ sk_B_1 @ sk_C_3)
% 0.90/1.17              = (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['82', '85'])).
% 0.90/1.17  thf('87', plain,
% 0.90/1.17      (![X14 : $i, X15 : $i]:
% 0.90/1.17         ((r1_xboole_0 @ X14 @ X15)
% 0.90/1.17          | (r2_hidden @ (sk_C_1 @ X15 @ X14) @ (k3_xboole_0 @ X14 @ X15)))),
% 0.90/1.17      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.90/1.17  thf('88', plain,
% 0.90/1.17      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.17  thf('89', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.90/1.17      inference('sup-', [status(thm)], ['87', '88'])).
% 0.90/1.17  thf('90', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (((k2_xboole_0 @ sk_B_1 @ sk_C_3)
% 0.90/1.17            = (k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))
% 0.90/1.17          | (r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3) @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['86', '89'])).
% 0.90/1.17  thf('91', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_3) = (sk_B_1))),
% 0.90/1.17      inference('sup-', [status(thm)], ['46', '49'])).
% 0.90/1.17  thf('92', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_3) = (sk_B_1))),
% 0.90/1.17      inference('sup-', [status(thm)], ['46', '49'])).
% 0.90/1.17  thf('93', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_3) = (sk_B_1))),
% 0.90/1.17      inference('sup-', [status(thm)], ['46', '49'])).
% 0.90/1.17  thf('94', plain,
% 0.90/1.17      (![X0 : $i]:
% 0.90/1.17         (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ X0))
% 0.90/1.17          | (r1_xboole_0 @ sk_B_1 @ X0))),
% 0.90/1.17      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.90/1.17  thf('95', plain, ((((sk_B_1) = (sk_C_3)) | (r1_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.90/1.17      inference('sup+', [status(thm)], ['68', '94'])).
% 0.90/1.17  thf('96', plain, (((sk_B_1) != (sk_C_3))),
% 0.90/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.17  thf('97', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_3)),
% 0.90/1.17      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.90/1.17  thf('98', plain,
% 0.90/1.17      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.90/1.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.17  thf('99', plain,
% 0.90/1.17      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.90/1.17         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 0.90/1.17          | ~ (r1_xboole_0 @ X14 @ X17))),
% 0.90/1.17      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.90/1.17  thf('100', plain,
% 0.90/1.17      (![X0 : $i, X1 : $i]:
% 0.90/1.17         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.90/1.17      inference('sup-', [status(thm)], ['98', '99'])).
% 0.90/1.17  thf('101', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.90/1.17      inference('sup-', [status(thm)], ['97', '100'])).
% 0.90/1.17  thf('102', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_3) = (sk_C_3))),
% 0.90/1.17      inference('demod', [status(thm)], ['54', '55', '67'])).
% 0.90/1.17  thf('103', plain, ((v1_xboole_0 @ sk_C_3)),
% 0.90/1.17      inference('demod', [status(thm)], ['101', '102'])).
% 0.90/1.17  thf('104', plain, ($false), inference('demod', [status(thm)], ['20', '103'])).
% 0.90/1.17  
% 0.90/1.17  % SZS output end Refutation
% 0.90/1.17  
% 1.00/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
