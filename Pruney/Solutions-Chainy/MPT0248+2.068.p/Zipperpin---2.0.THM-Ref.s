%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ersoIi7cLO

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:27 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  238 (3460 expanded)
%              Number of leaves         :   36 (1032 expanded)
%              Depth                    :   37
%              Number of atoms          : 1538 (32584 expanded)
%              Number of equality atoms :  225 (5534 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_2 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( X33 = X30 )
      | ( X32
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( sk_B @ sk_B_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ sk_A @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X63: $i,X65: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X63 ) @ X65 )
      | ~ ( r2_hidden @ X63 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_2 ) @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('35',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) ) )
      = X19 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('41',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','44'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_2 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X28 @ X29 ) @ ( k2_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('52',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('54',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_2 @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['50','54'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('56',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ X26 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_2 @ ( k3_xboole_0 @ sk_B_2 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_2 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('66',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ ( k4_xboole_0 @ sk_B_2 @ sk_C_2 ) )
    | ( ( k1_tarski @ sk_A )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('73',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('77',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('79',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_B_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('81',plain,
    ( ( r2_hidden @ sk_A @ sk_B_2 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X63: $i,X65: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X63 ) @ X65 )
      | ~ ( r2_hidden @ X63 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('84',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('86',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( sk_B_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['87'])).

thf('89',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('92',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( ( sk_B_2 != k1_xboole_0 )
      & ( sk_B_2
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['72','74','93'])).

thf('95',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['71','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ ( k4_xboole_0 @ sk_B_2 @ sk_C_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','95'])).

thf('97',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['49','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    r2_hidden @ ( sk_B @ sk_B_2 ) @ sk_B_2 ),
    inference(clc,[status(thm)],['25','98'])).

thf('100',plain,(
    r2_hidden @ ( sk_B @ sk_B_2 ) @ sk_B_2 ),
    inference(clc,[status(thm)],['25','98'])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('102',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_B @ sk_B_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    r2_hidden @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['99','106'])).

thf('108',plain,(
    ! [X63: $i,X65: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X63 ) @ X65 )
      | ~ ( r2_hidden @ X63 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('109',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_2 ),
    inference(demod,[status(thm)],['7','109'])).

thf('111',plain,
    ( sk_B_2
    = ( k3_tarski @ ( k2_tarski @ sk_B_2 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','110'])).

thf('112',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('113',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_2 @ ( k5_xboole_0 @ sk_C_2 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('116',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) ) )
      = X19 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('118',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_C_2 @ ( k4_xboole_0 @ sk_B_2 @ sk_C_2 ) ) )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('120',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('121',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    r1_tarski @ sk_C_2 @ sk_B_2 ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('124',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ sk_C_2 )
    | ( sk_B_2 = sk_C_2 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('126',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_xboole_0 @ X18 @ X17 )
        = X17 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('127',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X66: $i,X67: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X66 @ X67 ) )
      = ( k2_xboole_0 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('129',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k5_xboole_0 @ X29 @ ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('131',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_2 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('132',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('133',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('136',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('139',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    = sk_B_2 ),
    inference(demod,[status(thm)],['131','134','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','44'])).

thf('141',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['87'])).

thf('142',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_C_2
         != ( k3_xboole_0 @ X1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( sk_C_2 != sk_B_2 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_2 @ X0 )
        = X0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_2 @ ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['50','54'])).

thf('148',plain,
    ( ( ( k3_xboole_0 @ sk_B_2 @ sk_C_2 )
      = ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('151',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_B_2 @ X0 )
        = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('153',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ sk_B_2 @ X0 )
        = sk_B_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( sk_B_2
      = ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('156',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ sk_C_2 @ sk_B_2 ) )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('158',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('159',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B_2 )
        = X0 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
   <= ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','159'])).

thf('161',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['71','94'])).

thf('162',plain,
    ( sk_B_2
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['87'])).

thf('164',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( sk_C_2 != sk_B_2 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['143','164'])).

thf('166',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('167',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['71','94'])).

thf('168',plain,
    ( ( sk_C_2 != sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    sk_C_2 != sk_B_2 ),
    inference(clc,[status(thm)],['165','168'])).

thf('170',plain,(
    ~ ( r1_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['124','169'])).

thf('171',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('172',plain,(
    r1_tarski @ sk_C_2 @ sk_B_2 ),
    inference('sup+',[status(thm)],['118','121'])).

thf('173',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['171','174'])).

thf('176',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['87'])).

thf('177',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['162','163'])).

thf('178',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['176','177'])).

thf('179',plain,(
    r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['175','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('181',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_2 ),
    inference(demod,[status(thm)],['7','109'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('183',plain,
    ( ( k3_tarski @ sk_B_2 )
    = sk_A ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_tarski @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['180','183'])).

thf('185',plain,
    ( ( sk_B_1 @ sk_C_2 )
    = ( k3_tarski @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['179','184'])).

thf('186',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('187',plain,(
    ! [X63: $i,X65: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X63 ) @ X65 )
      | ~ ( r2_hidden @ X63 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['185','188'])).

thf('190',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['107','108'])).

thf('191',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('192',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( sk_B_2
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    r1_tarski @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('194',plain,
    ( sk_B_2
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( k3_tarski @ sk_B_2 )
    = sk_A ),
    inference('sup+',[status(thm)],['181','182'])).

thf('196',plain,
    ( sk_B_2
    = ( k1_tarski @ ( k3_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( r1_tarski @ sk_B_2 @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['189','196'])).

thf('198',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['176','177'])).

thf('199',plain,(
    r1_tarski @ sk_B_2 @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['197','198'])).

thf('200',plain,(
    $false ),
    inference(demod,[status(thm)],['170','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ersoIi7cLO
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.73/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.73/0.92  % Solved by: fo/fo7.sh
% 0.73/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.92  % done 1508 iterations in 0.465s
% 0.73/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.73/0.92  % SZS output start Refutation
% 0.73/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.92  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.73/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.73/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.73/0.92  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.73/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.73/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.73/0.92  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.73/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.73/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.73/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.73/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.73/0.92  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.73/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.73/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.73/0.92  thf(sk_B_type, type, sk_B: $i > $i).
% 0.73/0.92  thf(t43_zfmisc_1, conjecture,
% 0.73/0.92    (![A:$i,B:$i,C:$i]:
% 0.73/0.92     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.73/0.92          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.73/0.92          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.73/0.92          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.73/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.73/0.92        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.73/0.92             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.73/0.92             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.73/0.92             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.73/0.92    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.73/0.92  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf(l51_zfmisc_1, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.73/0.92  thf('1', plain,
% 0.73/0.92      (![X66 : $i, X67 : $i]:
% 0.73/0.92         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.73/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.92  thf('2', plain,
% 0.73/0.92      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_2 @ sk_C_2)))),
% 0.73/0.92      inference('demod', [status(thm)], ['0', '1'])).
% 0.73/0.92  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf(t7_xboole_1, axiom,
% 0.73/0.92    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.73/0.92  thf('4', plain,
% 0.73/0.92      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.73/0.92      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.73/0.92  thf('5', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.73/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.73/0.92  thf(d10_xboole_0, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.73/0.92  thf('6', plain,
% 0.73/0.92      (![X12 : $i, X14 : $i]:
% 0.73/0.92         (((X12) = (X14))
% 0.73/0.92          | ~ (r1_tarski @ X14 @ X12)
% 0.73/0.92          | ~ (r1_tarski @ X12 @ X14))),
% 0.73/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.73/0.92  thf('7', plain,
% 0.73/0.92      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.73/0.92        | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.73/0.92  thf(d1_xboole_0, axiom,
% 0.73/0.92    (![A:$i]:
% 0.73/0.92     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.73/0.92  thf('8', plain,
% 0.73/0.92      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.73/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.73/0.92  thf('9', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.73/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.73/0.92  thf(d3_tarski, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( r1_tarski @ A @ B ) <=>
% 0.73/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.73/0.92  thf('10', plain,
% 0.73/0.92      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.73/0.92         (~ (r2_hidden @ X5 @ X6)
% 0.73/0.92          | (r2_hidden @ X5 @ X7)
% 0.73/0.92          | ~ (r1_tarski @ X6 @ X7))),
% 0.73/0.92      inference('cnf', [status(esa)], [d3_tarski])).
% 0.73/0.92  thf('11', plain,
% 0.73/0.92      (![X0 : $i]:
% 0.73/0.92         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['9', '10'])).
% 0.73/0.92  thf('12', plain,
% 0.73/0.92      (((v1_xboole_0 @ sk_B_2)
% 0.73/0.92        | (r2_hidden @ (sk_B @ sk_B_2) @ (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['8', '11'])).
% 0.73/0.92  thf(d1_tarski, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.73/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.73/0.92  thf('13', plain,
% 0.73/0.92      (![X30 : $i, X32 : $i, X33 : $i]:
% 0.73/0.92         (~ (r2_hidden @ X33 @ X32)
% 0.73/0.92          | ((X33) = (X30))
% 0.73/0.92          | ((X32) != (k1_tarski @ X30)))),
% 0.73/0.92      inference('cnf', [status(esa)], [d1_tarski])).
% 0.73/0.92  thf('14', plain,
% 0.73/0.92      (![X30 : $i, X33 : $i]:
% 0.73/0.92         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 0.73/0.92      inference('simplify', [status(thm)], ['13'])).
% 0.73/0.92  thf('15', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_B @ sk_B_2) = (sk_A)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['12', '14'])).
% 0.73/0.92  thf('16', plain,
% 0.73/0.92      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.73/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.73/0.92  thf('17', plain,
% 0.73/0.92      (((r2_hidden @ sk_A @ sk_B_2)
% 0.73/0.92        | (v1_xboole_0 @ sk_B_2)
% 0.73/0.92        | (v1_xboole_0 @ sk_B_2))),
% 0.73/0.92      inference('sup+', [status(thm)], ['15', '16'])).
% 0.73/0.92  thf('18', plain, (((v1_xboole_0 @ sk_B_2) | (r2_hidden @ sk_A @ sk_B_2))),
% 0.73/0.92      inference('simplify', [status(thm)], ['17'])).
% 0.73/0.92  thf(l1_zfmisc_1, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.73/0.92  thf('19', plain,
% 0.73/0.92      (![X63 : $i, X65 : $i]:
% 0.73/0.92         ((r1_tarski @ (k1_tarski @ X63) @ X65) | ~ (r2_hidden @ X63 @ X65))),
% 0.73/0.92      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.73/0.92  thf('20', plain,
% 0.73/0.92      (((v1_xboole_0 @ sk_B_2) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['18', '19'])).
% 0.73/0.92  thf('21', plain,
% 0.73/0.92      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.73/0.92        | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.73/0.92  thf('22', plain,
% 0.73/0.92      (((v1_xboole_0 @ sk_B_2) | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['20', '21'])).
% 0.73/0.92  thf('23', plain,
% 0.73/0.92      (((v1_xboole_0 @ sk_B_2)
% 0.73/0.92        | (r2_hidden @ (sk_B @ sk_B_2) @ (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['8', '11'])).
% 0.73/0.92  thf('24', plain,
% 0.73/0.92      (((r2_hidden @ (sk_B @ sk_B_2) @ sk_B_2)
% 0.73/0.92        | (v1_xboole_0 @ sk_B_2)
% 0.73/0.92        | (v1_xboole_0 @ sk_B_2))),
% 0.73/0.92      inference('sup+', [status(thm)], ['22', '23'])).
% 0.73/0.92  thf('25', plain,
% 0.73/0.92      (((v1_xboole_0 @ sk_B_2) | (r2_hidden @ (sk_B @ sk_B_2) @ sk_B_2))),
% 0.73/0.92      inference('simplify', [status(thm)], ['24'])).
% 0.73/0.92  thf(t7_xboole_0, axiom,
% 0.73/0.92    (![A:$i]:
% 0.73/0.92     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.73/0.92          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.73/0.92  thf('26', plain,
% 0.73/0.92      (![X11 : $i]:
% 0.73/0.92         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X11) @ X11))),
% 0.73/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.73/0.92  thf('27', plain,
% 0.73/0.92      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.73/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.73/0.92  thf('28', plain,
% 0.73/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.73/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.73/0.92  thf(t100_xboole_1, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.73/0.92  thf('29', plain,
% 0.73/0.92      (![X15 : $i, X16 : $i]:
% 0.73/0.92         ((k4_xboole_0 @ X15 @ X16)
% 0.73/0.92           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.73/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.73/0.92  thf(commutativity_k5_xboole_0, axiom,
% 0.73/0.92    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.73/0.92  thf('30', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.73/0.92      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.73/0.92  thf(t5_boole, axiom,
% 0.73/0.92    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.73/0.92  thf('31', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.73/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.73/0.92  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['30', '31'])).
% 0.73/0.92  thf('33', plain,
% 0.73/0.92      (![X0 : $i]:
% 0.73/0.92         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['29', '32'])).
% 0.73/0.92  thf(t51_xboole_1, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.73/0.92       ( A ) ))).
% 0.73/0.92  thf('34', plain,
% 0.73/0.92      (![X19 : $i, X20 : $i]:
% 0.73/0.92         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.73/0.92           = (X19))),
% 0.73/0.92      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.73/0.92  thf('35', plain,
% 0.73/0.92      (![X66 : $i, X67 : $i]:
% 0.73/0.92         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.73/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.92  thf('36', plain,
% 0.73/0.92      (![X19 : $i, X20 : $i]:
% 0.73/0.92         ((k3_tarski @ 
% 0.73/0.92           (k2_tarski @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20)))
% 0.73/0.92           = (X19))),
% 0.73/0.92      inference('demod', [status(thm)], ['34', '35'])).
% 0.73/0.92  thf('37', plain,
% 0.73/0.92      (![X0 : $i]:
% 0.73/0.92         ((k3_tarski @ 
% 0.73/0.92           (k2_tarski @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ 
% 0.73/0.92            (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 0.73/0.92           = (k1_xboole_0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['33', '36'])).
% 0.73/0.92  thf(t69_enumset1, axiom,
% 0.73/0.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.73/0.92  thf('38', plain,
% 0.73/0.92      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.73/0.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.73/0.92  thf('39', plain,
% 0.73/0.92      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.73/0.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.73/0.92  thf(idempotence_k2_xboole_0, axiom,
% 0.73/0.92    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.73/0.92  thf('40', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 0.73/0.92      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.73/0.92  thf('41', plain,
% 0.73/0.92      (![X66 : $i, X67 : $i]:
% 0.73/0.92         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.73/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.92  thf('42', plain, (![X9 : $i]: ((k3_tarski @ (k2_tarski @ X9 @ X9)) = (X9))),
% 0.73/0.92      inference('demod', [status(thm)], ['40', '41'])).
% 0.73/0.92  thf('43', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['39', '42'])).
% 0.73/0.92  thf('44', plain,
% 0.73/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.73/0.92      inference('demod', [status(thm)], ['37', '38', '43'])).
% 0.73/0.92  thf('45', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['28', '44'])).
% 0.73/0.92  thf('46', plain,
% 0.73/0.92      (![X15 : $i, X16 : $i]:
% 0.73/0.92         ((k4_xboole_0 @ X15 @ X16)
% 0.73/0.92           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.73/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.73/0.92  thf('47', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         (((k4_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.73/0.92          | ~ (v1_xboole_0 @ X1))),
% 0.73/0.92      inference('sup+', [status(thm)], ['45', '46'])).
% 0.73/0.92  thf('48', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.73/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.73/0.92  thf('49', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         (((k4_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.73/0.92      inference('demod', [status(thm)], ['47', '48'])).
% 0.73/0.92  thf('50', plain,
% 0.73/0.92      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_2 @ sk_C_2)))),
% 0.73/0.92      inference('demod', [status(thm)], ['0', '1'])).
% 0.73/0.92  thf(t95_xboole_1, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( k3_xboole_0 @ A @ B ) =
% 0.73/0.92       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.73/0.92  thf('51', plain,
% 0.73/0.92      (![X28 : $i, X29 : $i]:
% 0.73/0.92         ((k3_xboole_0 @ X28 @ X29)
% 0.73/0.92           = (k5_xboole_0 @ (k5_xboole_0 @ X28 @ X29) @ 
% 0.73/0.92              (k2_xboole_0 @ X28 @ X29)))),
% 0.73/0.92      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.73/0.92  thf('52', plain,
% 0.73/0.92      (![X66 : $i, X67 : $i]:
% 0.73/0.92         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.73/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.92  thf(t91_xboole_1, axiom,
% 0.73/0.92    (![A:$i,B:$i,C:$i]:
% 0.73/0.92     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.73/0.92       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.73/0.92  thf('53', plain,
% 0.73/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.73/0.92         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 0.73/0.92           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 0.73/0.92      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.73/0.92  thf('54', plain,
% 0.73/0.92      (![X28 : $i, X29 : $i]:
% 0.73/0.92         ((k3_xboole_0 @ X28 @ X29)
% 0.73/0.92           = (k5_xboole_0 @ X28 @ 
% 0.73/0.92              (k5_xboole_0 @ X29 @ (k3_tarski @ (k2_tarski @ X28 @ X29)))))),
% 0.73/0.92      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.73/0.92  thf('55', plain,
% 0.73/0.92      (((k3_xboole_0 @ sk_B_2 @ sk_C_2)
% 0.73/0.92         = (k5_xboole_0 @ sk_B_2 @ (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup+', [status(thm)], ['50', '54'])).
% 0.73/0.92  thf(t92_xboole_1, axiom,
% 0.73/0.92    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.73/0.92  thf('56', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ X27) = (k1_xboole_0))),
% 0.73/0.92      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.73/0.92  thf('57', plain,
% 0.73/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.73/0.92         ((k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ X26)
% 0.73/0.92           = (k5_xboole_0 @ X24 @ (k5_xboole_0 @ X25 @ X26)))),
% 0.73/0.92      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.73/0.92  thf('58', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.73/0.92           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.73/0.92      inference('sup+', [status(thm)], ['56', '57'])).
% 0.73/0.92  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['30', '31'])).
% 0.73/0.92  thf('60', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.73/0.92      inference('demod', [status(thm)], ['58', '59'])).
% 0.73/0.92  thf('61', plain,
% 0.73/0.92      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.73/0.92         = (k5_xboole_0 @ sk_B_2 @ (k3_xboole_0 @ sk_B_2 @ sk_C_2)))),
% 0.73/0.92      inference('sup+', [status(thm)], ['55', '60'])).
% 0.73/0.92  thf('62', plain,
% 0.73/0.92      (![X15 : $i, X16 : $i]:
% 0.73/0.92         ((k4_xboole_0 @ X15 @ X16)
% 0.73/0.92           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.73/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.73/0.92  thf('63', plain,
% 0.73/0.92      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.73/0.92         = (k4_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.73/0.92      inference('demod', [status(thm)], ['61', '62'])).
% 0.73/0.92  thf('64', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.73/0.92      inference('demod', [status(thm)], ['58', '59'])).
% 0.73/0.92  thf('65', plain,
% 0.73/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.73/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.73/0.92  thf('66', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.73/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.73/0.92  thf('67', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         (((k5_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['65', '66'])).
% 0.73/0.92  thf('68', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         (((X0) = (X1)) | ~ (v1_xboole_0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.73/0.92      inference('sup+', [status(thm)], ['64', '67'])).
% 0.73/0.92  thf('69', plain,
% 0.73/0.92      ((~ (v1_xboole_0 @ (k4_xboole_0 @ sk_B_2 @ sk_C_2))
% 0.73/0.92        | ((k1_tarski @ sk_A) = (sk_C_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['63', '68'])).
% 0.73/0.92  thf('70', plain,
% 0.73/0.92      ((((sk_B_2) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('71', plain,
% 0.73/0.92      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.73/0.92         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('split', [status(esa)], ['70'])).
% 0.73/0.92  thf('72', plain,
% 0.73/0.92      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_2) = (k1_xboole_0)))),
% 0.73/0.92      inference('split', [status(esa)], ['70'])).
% 0.73/0.92  thf('73', plain,
% 0.73/0.92      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('74', plain,
% 0.73/0.92      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.73/0.92       ~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('split', [status(esa)], ['73'])).
% 0.73/0.92  thf('75', plain,
% 0.73/0.92      (![X11 : $i]:
% 0.73/0.92         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X11) @ X11))),
% 0.73/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.73/0.92  thf('76', plain,
% 0.73/0.92      (![X0 : $i]:
% 0.73/0.92         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['9', '10'])).
% 0.73/0.92  thf('77', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0))
% 0.73/0.92        | (r2_hidden @ (sk_B_1 @ sk_B_2) @ (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['75', '76'])).
% 0.73/0.92  thf('78', plain,
% 0.73/0.92      (![X30 : $i, X33 : $i]:
% 0.73/0.92         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 0.73/0.92      inference('simplify', [status(thm)], ['13'])).
% 0.73/0.92  thf('79', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0)) | ((sk_B_1 @ sk_B_2) = (sk_A)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['77', '78'])).
% 0.73/0.92  thf('80', plain,
% 0.73/0.92      (![X11 : $i]:
% 0.73/0.92         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X11) @ X11))),
% 0.73/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.73/0.92  thf('81', plain,
% 0.73/0.92      (((r2_hidden @ sk_A @ sk_B_2)
% 0.73/0.92        | ((sk_B_2) = (k1_xboole_0))
% 0.73/0.92        | ((sk_B_2) = (k1_xboole_0)))),
% 0.73/0.92      inference('sup+', [status(thm)], ['79', '80'])).
% 0.73/0.92  thf('82', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_2))),
% 0.73/0.92      inference('simplify', [status(thm)], ['81'])).
% 0.73/0.92  thf('83', plain,
% 0.73/0.92      (![X63 : $i, X65 : $i]:
% 0.73/0.92         ((r1_tarski @ (k1_tarski @ X63) @ X65) | ~ (r2_hidden @ X63 @ X65))),
% 0.73/0.92      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.73/0.92  thf('84', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['82', '83'])).
% 0.73/0.92  thf('85', plain,
% 0.73/0.92      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.73/0.92        | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['5', '6'])).
% 0.73/0.92  thf('86', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0)) | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['84', '85'])).
% 0.73/0.92  thf('87', plain,
% 0.73/0.92      ((((sk_B_2) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.73/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.92  thf('88', plain,
% 0.73/0.92      ((((sk_B_2) != (k1_tarski @ sk_A)))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('split', [status(esa)], ['87'])).
% 0.73/0.92  thf('89', plain,
% 0.73/0.92      (((((sk_B_2) != (sk_B_2)) | ((sk_B_2) = (k1_xboole_0))))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup-', [status(thm)], ['86', '88'])).
% 0.73/0.92  thf('90', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('simplify', [status(thm)], ['89'])).
% 0.73/0.92  thf('91', plain,
% 0.73/0.92      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.73/0.92      inference('split', [status(esa)], ['70'])).
% 0.73/0.92  thf('92', plain,
% 0.73/0.92      ((((sk_B_2) != (sk_B_2)))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_xboole_0))) & 
% 0.73/0.92             ~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup-', [status(thm)], ['90', '91'])).
% 0.73/0.92  thf('93', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0))) | (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('simplify', [status(thm)], ['92'])).
% 0.73/0.92  thf('94', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('sat_resolution*', [status(thm)], ['72', '74', '93'])).
% 0.73/0.92  thf('95', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.73/0.92      inference('simpl_trail', [status(thm)], ['71', '94'])).
% 0.73/0.92  thf('96', plain, (~ (v1_xboole_0 @ (k4_xboole_0 @ sk_B_2 @ sk_C_2))),
% 0.73/0.92      inference('simplify_reflect-', [status(thm)], ['69', '95'])).
% 0.73/0.92  thf('97', plain, ((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['49', '96'])).
% 0.73/0.92  thf('98', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.73/0.92      inference('simplify', [status(thm)], ['97'])).
% 0.73/0.92  thf('99', plain, ((r2_hidden @ (sk_B @ sk_B_2) @ sk_B_2)),
% 0.73/0.92      inference('clc', [status(thm)], ['25', '98'])).
% 0.73/0.92  thf('100', plain, ((r2_hidden @ (sk_B @ sk_B_2) @ sk_B_2)),
% 0.73/0.92      inference('clc', [status(thm)], ['25', '98'])).
% 0.73/0.92  thf('101', plain,
% 0.73/0.92      (((v1_xboole_0 @ sk_B_2) | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['20', '21'])).
% 0.73/0.92  thf('102', plain,
% 0.73/0.92      (![X30 : $i, X33 : $i]:
% 0.73/0.92         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 0.73/0.92      inference('simplify', [status(thm)], ['13'])).
% 0.73/0.92  thf('103', plain,
% 0.73/0.92      (![X0 : $i]:
% 0.73/0.92         (~ (r2_hidden @ X0 @ sk_B_2)
% 0.73/0.92          | (v1_xboole_0 @ sk_B_2)
% 0.73/0.92          | ((X0) = (sk_A)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['101', '102'])).
% 0.73/0.92  thf('104', plain,
% 0.73/0.92      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.73/0.92      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.73/0.92  thf('105', plain,
% 0.73/0.92      (![X0 : $i]: (((X0) = (sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.73/0.92      inference('clc', [status(thm)], ['103', '104'])).
% 0.73/0.92  thf('106', plain, (((sk_B @ sk_B_2) = (sk_A))),
% 0.73/0.92      inference('sup-', [status(thm)], ['100', '105'])).
% 0.73/0.92  thf('107', plain, ((r2_hidden @ sk_A @ sk_B_2)),
% 0.73/0.92      inference('demod', [status(thm)], ['99', '106'])).
% 0.73/0.92  thf('108', plain,
% 0.73/0.92      (![X63 : $i, X65 : $i]:
% 0.73/0.92         ((r1_tarski @ (k1_tarski @ X63) @ X65) | ~ (r2_hidden @ X63 @ X65))),
% 0.73/0.92      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.73/0.92  thf('109', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.73/0.92      inference('sup-', [status(thm)], ['107', '108'])).
% 0.73/0.92  thf('110', plain, (((k1_tarski @ sk_A) = (sk_B_2))),
% 0.73/0.92      inference('demod', [status(thm)], ['7', '109'])).
% 0.73/0.92  thf('111', plain, (((sk_B_2) = (k3_tarski @ (k2_tarski @ sk_B_2 @ sk_C_2)))),
% 0.73/0.92      inference('demod', [status(thm)], ['2', '110'])).
% 0.73/0.92  thf('112', plain,
% 0.73/0.92      (![X28 : $i, X29 : $i]:
% 0.73/0.92         ((k3_xboole_0 @ X28 @ X29)
% 0.73/0.92           = (k5_xboole_0 @ X28 @ 
% 0.73/0.92              (k5_xboole_0 @ X29 @ (k3_tarski @ (k2_tarski @ X28 @ X29)))))),
% 0.73/0.92      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.73/0.92  thf('113', plain,
% 0.73/0.92      (((k3_xboole_0 @ sk_B_2 @ sk_C_2)
% 0.73/0.92         = (k5_xboole_0 @ sk_B_2 @ (k5_xboole_0 @ sk_C_2 @ sk_B_2)))),
% 0.73/0.92      inference('sup+', [status(thm)], ['111', '112'])).
% 0.73/0.92  thf('114', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.73/0.92      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.73/0.92  thf('115', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.73/0.92      inference('demod', [status(thm)], ['58', '59'])).
% 0.73/0.92  thf('116', plain, (((k3_xboole_0 @ sk_B_2 @ sk_C_2) = (sk_C_2))),
% 0.73/0.92      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.73/0.92  thf('117', plain,
% 0.73/0.92      (![X19 : $i, X20 : $i]:
% 0.73/0.92         ((k3_tarski @ 
% 0.73/0.92           (k2_tarski @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20)))
% 0.73/0.92           = (X19))),
% 0.73/0.92      inference('demod', [status(thm)], ['34', '35'])).
% 0.73/0.92  thf('118', plain,
% 0.73/0.92      (((k3_tarski @ (k2_tarski @ sk_C_2 @ (k4_xboole_0 @ sk_B_2 @ sk_C_2)))
% 0.73/0.92         = (sk_B_2))),
% 0.73/0.92      inference('sup+', [status(thm)], ['116', '117'])).
% 0.73/0.92  thf('119', plain,
% 0.73/0.92      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.73/0.92      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.73/0.92  thf('120', plain,
% 0.73/0.92      (![X66 : $i, X67 : $i]:
% 0.73/0.92         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.73/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.92  thf('121', plain,
% 0.73/0.92      (![X22 : $i, X23 : $i]:
% 0.73/0.92         (r1_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X22 @ X23)))),
% 0.73/0.92      inference('demod', [status(thm)], ['119', '120'])).
% 0.73/0.92  thf('122', plain, ((r1_tarski @ sk_C_2 @ sk_B_2)),
% 0.73/0.92      inference('sup+', [status(thm)], ['118', '121'])).
% 0.73/0.92  thf('123', plain,
% 0.73/0.92      (![X12 : $i, X14 : $i]:
% 0.73/0.92         (((X12) = (X14))
% 0.73/0.92          | ~ (r1_tarski @ X14 @ X12)
% 0.73/0.92          | ~ (r1_tarski @ X12 @ X14))),
% 0.73/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.73/0.92  thf('124', plain,
% 0.73/0.92      ((~ (r1_tarski @ sk_B_2 @ sk_C_2) | ((sk_B_2) = (sk_C_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['122', '123'])).
% 0.73/0.92  thf('125', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.73/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.73/0.92  thf(t12_xboole_1, axiom,
% 0.73/0.92    (![A:$i,B:$i]:
% 0.73/0.92     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.73/0.92  thf('126', plain,
% 0.73/0.92      (![X17 : $i, X18 : $i]:
% 0.73/0.92         (((k2_xboole_0 @ X18 @ X17) = (X17)) | ~ (r1_tarski @ X18 @ X17))),
% 0.73/0.92      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.73/0.92  thf('127', plain,
% 0.73/0.92      (((k2_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.73/0.92      inference('sup-', [status(thm)], ['125', '126'])).
% 0.73/0.92  thf('128', plain,
% 0.73/0.92      (![X66 : $i, X67 : $i]:
% 0.73/0.92         ((k3_tarski @ (k2_tarski @ X66 @ X67)) = (k2_xboole_0 @ X66 @ X67))),
% 0.73/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.73/0.92  thf('129', plain,
% 0.73/0.92      (((k3_tarski @ (k2_tarski @ sk_B_2 @ (k1_tarski @ sk_A)))
% 0.73/0.92         = (k1_tarski @ sk_A))),
% 0.73/0.92      inference('demod', [status(thm)], ['127', '128'])).
% 0.73/0.92  thf('130', plain,
% 0.73/0.92      (![X28 : $i, X29 : $i]:
% 0.73/0.92         ((k3_xboole_0 @ X28 @ X29)
% 0.73/0.92           = (k5_xboole_0 @ X28 @ 
% 0.73/0.92              (k5_xboole_0 @ X29 @ (k3_tarski @ (k2_tarski @ X28 @ X29)))))),
% 0.73/0.92      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.73/0.92  thf('131', plain,
% 0.73/0.92      (((k3_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.73/0.92         = (k5_xboole_0 @ sk_B_2 @ 
% 0.73/0.92            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup+', [status(thm)], ['129', '130'])).
% 0.73/0.92  thf(idempotence_k3_xboole_0, axiom,
% 0.73/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.73/0.92  thf('132', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.73/0.92      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.73/0.92  thf('133', plain,
% 0.73/0.92      (![X15 : $i, X16 : $i]:
% 0.73/0.92         ((k4_xboole_0 @ X15 @ X16)
% 0.73/0.92           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.73/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.73/0.92  thf('134', plain,
% 0.73/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['132', '133'])).
% 0.73/0.92  thf('135', plain,
% 0.73/0.92      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['132', '133'])).
% 0.73/0.92  thf('136', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ X27) = (k1_xboole_0))),
% 0.73/0.92      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.73/0.92  thf('137', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['135', '136'])).
% 0.73/0.92  thf('138', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.73/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.73/0.92  thf('139', plain, (((k3_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A)) = (sk_B_2))),
% 0.73/0.92      inference('demod', [status(thm)], ['131', '134', '137', '138'])).
% 0.73/0.92  thf('140', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['28', '44'])).
% 0.73/0.92  thf('141', plain,
% 0.73/0.92      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.73/0.92      inference('split', [status(esa)], ['87'])).
% 0.73/0.92  thf('142', plain,
% 0.73/0.92      ((![X0 : $i, X1 : $i]:
% 0.73/0.92          (((sk_C_2) != (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1)))
% 0.73/0.92         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.73/0.92      inference('sup-', [status(thm)], ['140', '141'])).
% 0.73/0.92  thf('143', plain,
% 0.73/0.92      (((((sk_C_2) != (sk_B_2)) | ~ (v1_xboole_0 @ sk_B_2)))
% 0.73/0.92         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.73/0.92      inference('sup-', [status(thm)], ['139', '142'])).
% 0.73/0.92  thf('144', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('simplify', [status(thm)], ['89'])).
% 0.73/0.92  thf('145', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['30', '31'])).
% 0.73/0.92  thf('146', plain,
% 0.73/0.92      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_2 @ X0) = (X0)))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup+', [status(thm)], ['144', '145'])).
% 0.73/0.92  thf('147', plain,
% 0.73/0.92      (((k3_xboole_0 @ sk_B_2 @ sk_C_2)
% 0.73/0.92         = (k5_xboole_0 @ sk_B_2 @ (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup+', [status(thm)], ['50', '54'])).
% 0.73/0.92  thf('148', plain,
% 0.73/0.92      ((((k3_xboole_0 @ sk_B_2 @ sk_C_2)
% 0.73/0.92          = (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup+', [status(thm)], ['146', '147'])).
% 0.73/0.92  thf('149', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('simplify', [status(thm)], ['89'])).
% 0.73/0.92  thf('150', plain,
% 0.73/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.73/0.92      inference('demod', [status(thm)], ['37', '38', '43'])).
% 0.73/0.92  thf('151', plain,
% 0.73/0.92      ((![X0 : $i]: ((k3_xboole_0 @ sk_B_2 @ X0) = (k1_xboole_0)))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup+', [status(thm)], ['149', '150'])).
% 0.73/0.92  thf('152', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('simplify', [status(thm)], ['89'])).
% 0.73/0.92  thf('153', plain,
% 0.73/0.92      ((![X0 : $i]: ((k3_xboole_0 @ sk_B_2 @ X0) = (sk_B_2)))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('demod', [status(thm)], ['151', '152'])).
% 0.73/0.92  thf('154', plain,
% 0.73/0.92      ((((sk_B_2) = (k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('demod', [status(thm)], ['148', '153'])).
% 0.73/0.92  thf('155', plain,
% 0.73/0.92      (![X0 : $i, X1 : $i]:
% 0.73/0.92         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.73/0.92      inference('demod', [status(thm)], ['58', '59'])).
% 0.73/0.92  thf('156', plain,
% 0.73/0.92      ((((k1_tarski @ sk_A) = (k5_xboole_0 @ sk_C_2 @ sk_B_2)))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup+', [status(thm)], ['154', '155'])).
% 0.73/0.92  thf('157', plain,
% 0.73/0.92      ((((sk_B_2) = (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('simplify', [status(thm)], ['89'])).
% 0.73/0.92  thf('158', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.73/0.92      inference('cnf', [status(esa)], [t5_boole])).
% 0.73/0.92  thf('159', plain,
% 0.73/0.92      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B_2) = (X0)))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('sup+', [status(thm)], ['157', '158'])).
% 0.73/0.92  thf('160', plain,
% 0.73/0.92      ((((k1_tarski @ sk_A) = (sk_C_2)))
% 0.73/0.92         <= (~ (((sk_B_2) = (k1_tarski @ sk_A))))),
% 0.73/0.92      inference('demod', [status(thm)], ['156', '159'])).
% 0.73/0.92  thf('161', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.73/0.92      inference('simpl_trail', [status(thm)], ['71', '94'])).
% 0.73/0.92  thf('162', plain, ((((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('simplify_reflect-', [status(thm)], ['160', '161'])).
% 0.73/0.92  thf('163', plain,
% 0.73/0.92      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('split', [status(esa)], ['87'])).
% 0.73/0.92  thf('164', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.73/0.92      inference('sat_resolution*', [status(thm)], ['162', '163'])).
% 0.73/0.92  thf('165', plain, ((((sk_C_2) != (sk_B_2)) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.73/0.92      inference('simpl_trail', [status(thm)], ['143', '164'])).
% 0.73/0.92  thf('166', plain,
% 0.73/0.92      (((v1_xboole_0 @ sk_B_2) | ((k1_tarski @ sk_A) = (sk_B_2)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['20', '21'])).
% 0.73/0.92  thf('167', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.73/0.92      inference('simpl_trail', [status(thm)], ['71', '94'])).
% 0.73/0.92  thf('168', plain, ((((sk_C_2) != (sk_B_2)) | (v1_xboole_0 @ sk_B_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['166', '167'])).
% 0.73/0.92  thf('169', plain, (((sk_C_2) != (sk_B_2))),
% 0.73/0.92      inference('clc', [status(thm)], ['165', '168'])).
% 0.73/0.92  thf('170', plain, (~ (r1_tarski @ sk_B_2 @ sk_C_2)),
% 0.73/0.92      inference('simplify_reflect-', [status(thm)], ['124', '169'])).
% 0.73/0.92  thf('171', plain,
% 0.73/0.92      (![X11 : $i]:
% 0.73/0.92         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X11) @ X11))),
% 0.73/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.73/0.92  thf('172', plain, ((r1_tarski @ sk_C_2 @ sk_B_2)),
% 0.73/0.92      inference('sup+', [status(thm)], ['118', '121'])).
% 0.73/0.92  thf('173', plain,
% 0.73/0.92      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.73/0.92         (~ (r2_hidden @ X5 @ X6)
% 0.73/0.92          | (r2_hidden @ X5 @ X7)
% 0.73/0.92          | ~ (r1_tarski @ X6 @ X7))),
% 0.73/0.92      inference('cnf', [status(esa)], [d3_tarski])).
% 0.73/0.92  thf('174', plain,
% 0.73/0.92      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['172', '173'])).
% 0.73/0.92  thf('175', plain,
% 0.73/0.92      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ sk_C_2) @ sk_B_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['171', '174'])).
% 0.73/0.92  thf('176', plain,
% 0.73/0.92      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.73/0.92      inference('split', [status(esa)], ['87'])).
% 0.73/0.92  thf('177', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.73/0.92      inference('sat_resolution*', [status(thm)], ['162', '163'])).
% 0.73/0.92  thf('178', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.73/0.92      inference('simpl_trail', [status(thm)], ['176', '177'])).
% 0.73/0.92  thf('179', plain, ((r2_hidden @ (sk_B_1 @ sk_C_2) @ sk_B_2)),
% 0.73/0.92      inference('simplify_reflect-', [status(thm)], ['175', '178'])).
% 0.73/0.92  thf('180', plain,
% 0.73/0.92      (![X0 : $i]: (((X0) = (sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.73/0.92      inference('clc', [status(thm)], ['103', '104'])).
% 0.73/0.92  thf('181', plain, (((k1_tarski @ sk_A) = (sk_B_2))),
% 0.73/0.92      inference('demod', [status(thm)], ['7', '109'])).
% 0.73/0.92  thf('182', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.73/0.92      inference('sup+', [status(thm)], ['39', '42'])).
% 0.73/0.92  thf('183', plain, (((k3_tarski @ sk_B_2) = (sk_A))),
% 0.73/0.92      inference('sup+', [status(thm)], ['181', '182'])).
% 0.73/0.92  thf('184', plain,
% 0.73/0.92      (![X0 : $i]:
% 0.73/0.92         (((X0) = (k3_tarski @ sk_B_2)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.73/0.92      inference('demod', [status(thm)], ['180', '183'])).
% 0.73/0.92  thf('185', plain, (((sk_B_1 @ sk_C_2) = (k3_tarski @ sk_B_2))),
% 0.73/0.92      inference('sup-', [status(thm)], ['179', '184'])).
% 0.73/0.92  thf('186', plain,
% 0.73/0.92      (![X11 : $i]:
% 0.73/0.92         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X11) @ X11))),
% 0.73/0.92      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.73/0.92  thf('187', plain,
% 0.73/0.92      (![X63 : $i, X65 : $i]:
% 0.73/0.92         ((r1_tarski @ (k1_tarski @ X63) @ X65) | ~ (r2_hidden @ X63 @ X65))),
% 0.73/0.92      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.73/0.92  thf('188', plain,
% 0.73/0.92      (![X0 : $i]:
% 0.73/0.92         (((X0) = (k1_xboole_0))
% 0.73/0.92          | (r1_tarski @ (k1_tarski @ (sk_B_1 @ X0)) @ X0))),
% 0.73/0.92      inference('sup-', [status(thm)], ['186', '187'])).
% 0.73/0.92  thf('189', plain,
% 0.73/0.92      (((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_2)) @ sk_C_2)
% 0.73/0.92        | ((sk_C_2) = (k1_xboole_0)))),
% 0.73/0.92      inference('sup+', [status(thm)], ['185', '188'])).
% 0.73/0.92  thf('190', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.73/0.92      inference('sup-', [status(thm)], ['107', '108'])).
% 0.73/0.92  thf('191', plain,
% 0.73/0.92      (![X12 : $i, X14 : $i]:
% 0.73/0.92         (((X12) = (X14))
% 0.73/0.92          | ~ (r1_tarski @ X14 @ X12)
% 0.73/0.92          | ~ (r1_tarski @ X12 @ X14))),
% 0.73/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.73/0.92  thf('192', plain,
% 0.73/0.92      ((~ (r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.73/0.92        | ((sk_B_2) = (k1_tarski @ sk_A)))),
% 0.73/0.92      inference('sup-', [status(thm)], ['190', '191'])).
% 0.73/0.92  thf('193', plain, ((r1_tarski @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.73/0.92      inference('sup+', [status(thm)], ['3', '4'])).
% 0.73/0.92  thf('194', plain, (((sk_B_2) = (k1_tarski @ sk_A))),
% 0.73/0.92      inference('demod', [status(thm)], ['192', '193'])).
% 0.73/0.92  thf('195', plain, (((k3_tarski @ sk_B_2) = (sk_A))),
% 0.73/0.92      inference('sup+', [status(thm)], ['181', '182'])).
% 0.73/0.92  thf('196', plain, (((sk_B_2) = (k1_tarski @ (k3_tarski @ sk_B_2)))),
% 0.73/0.92      inference('demod', [status(thm)], ['194', '195'])).
% 0.73/0.92  thf('197', plain,
% 0.73/0.92      (((r1_tarski @ sk_B_2 @ sk_C_2) | ((sk_C_2) = (k1_xboole_0)))),
% 0.73/0.92      inference('demod', [status(thm)], ['189', '196'])).
% 0.73/0.92  thf('198', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.73/0.92      inference('simpl_trail', [status(thm)], ['176', '177'])).
% 0.73/0.92  thf('199', plain, ((r1_tarski @ sk_B_2 @ sk_C_2)),
% 0.73/0.92      inference('simplify_reflect-', [status(thm)], ['197', '198'])).
% 0.73/0.92  thf('200', plain, ($false), inference('demod', [status(thm)], ['170', '199'])).
% 0.73/0.92  
% 0.73/0.92  % SZS output end Refutation
% 0.73/0.92  
% 0.77/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
