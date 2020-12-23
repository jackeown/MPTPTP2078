%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uT5ciAOgeV

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:35 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  166 (1816 expanded)
%              Number of leaves         :   29 ( 532 expanded)
%              Depth                    :   23
%              Number of atoms          : 1182 (18041 expanded)
%              Number of equality atoms :  178 (2902 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

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
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X32: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ X34 )
      | ( X35 = X32 )
      | ( X34
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X32: $i,X35: $i] :
      ( ( X35 = X32 )
      | ~ ( r2_hidden @ X35 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X32: $i,X35: $i] :
      ( ( X35 = X32 )
      | ~ ( r2_hidden @ X35 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_C_2 = k1_xboole_0 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X30 @ X31 ) @ ( k2_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k5_xboole_0 @ X31 @ ( k2_xboole_0 @ X30 @ X31 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('49',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('52',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('53',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_C_2 @ X0 )
        = X0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','54'])).

thf('56',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k5_xboole_0 @ X31 @ ( k2_xboole_0 @ X30 @ X31 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k5_xboole_0 @ sk_C_2 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('66',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['55','66'])).

thf('68',plain,
    ( ( sk_C_2
     != ( k4_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','67'])).

thf('69',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('70',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('71',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( r2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X32: $i,X35: $i] :
      ( ( X35 = X32 )
      | ~ ( r2_hidden @ X35 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('76',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('78',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('81',plain,(
    ! [X32: $i,X35: $i] :
      ( ( X35 = X32 )
      | ~ ( r2_hidden @ X35 @ ( k1_tarski @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('88',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('90',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_xboole_0 @ X21 @ X20 )
        = X20 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('95',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('98',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['93','96','99'])).

thf(t105_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( ( k4_xboole_0 @ B @ A )
          = k1_xboole_0 ) ) )).

thf('101',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_xboole_0 @ X18 @ X19 )
      | ( ( k4_xboole_0 @ X19 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t105_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ~ ( r2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','103'])).

thf('105',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','104'])).

thf('106',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('111',plain,
    ( ( sk_C_2 = sk_B_1 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['106'])).

thf('113',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('116',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['106'])).

thf('117',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( ( sk_C_2
       != ( k1_tarski @ sk_A ) )
      & ( sk_C_2 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('120',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('121',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['112','114','118','122','123'])).

thf('125',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['112','114','118'])).

thf('126',plain,(
    sk_C_2 = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['111','124','125'])).

thf('127',plain,(
    sk_C_2 = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['111','124','125'])).

thf('128',plain,
    ( ( sk_C_2 = k1_xboole_0 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = sk_C_2 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    sk_C_2 = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['111','124','125'])).

thf('132',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','126','127','130','131'])).

thf('133',plain,
    ( $false
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['112','114','118','122','123'])).

thf('135',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['133','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uT5ciAOgeV
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 846 iterations in 0.281s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.73  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.50/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.50/0.73  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.50/0.73  thf(t43_zfmisc_1, conjecture,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.50/0.73          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.50/0.73          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.50/0.73          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.73        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.50/0.73             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.50/0.73             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.50/0.73             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.50/0.73  thf('0', plain,
% 0.50/0.73      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.50/0.73         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.73      inference('split', [status(esa)], ['0'])).
% 0.50/0.73  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(d3_tarski, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X1 : $i, X3 : $i]:
% 0.50/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.73  thf(d3_xboole_0, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.50/0.73       ( ![D:$i]:
% 0.50/0.73         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.73           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X4 @ X5)
% 0.50/0.73          | (r2_hidden @ X4 @ X6)
% 0.50/0.73          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.50/0.73  thf('5', plain,
% 0.50/0.73      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.50/0.73         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.50/0.73      inference('simplify', [status(thm)], ['4'])).
% 0.50/0.73  thf('6', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         ((r1_tarski @ X0 @ X1)
% 0.50/0.73          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['3', '5'])).
% 0.50/0.73  thf('7', plain,
% 0.50/0.73      (![X1 : $i, X3 : $i]:
% 0.50/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.73  thf('8', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.50/0.73          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['8'])).
% 0.50/0.73  thf('10', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.50/0.73      inference('sup+', [status(thm)], ['2', '9'])).
% 0.50/0.73  thf(t12_xboole_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.50/0.73  thf('11', plain,
% 0.50/0.73      (![X20 : $i, X21 : $i]:
% 0.50/0.73         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 0.50/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.73  thf('12', plain,
% 0.50/0.73      (((k2_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.50/0.73      inference('sup-', [status(thm)], ['10', '11'])).
% 0.50/0.73  thf(t7_xboole_0, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.50/0.73          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      (![X15 : $i]:
% 0.50/0.73         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.50/0.73      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.50/0.73  thf(t7_xboole_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.50/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.50/0.73  thf('15', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.73          | (r2_hidden @ X0 @ X2)
% 0.50/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.73  thf('16', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.73  thf('17', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (((X0) = (k1_xboole_0))
% 0.50/0.73          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['13', '16'])).
% 0.50/0.73  thf('18', plain,
% 0.50/0.73      (((r2_hidden @ (sk_B @ sk_C_2) @ (k1_tarski @ sk_A))
% 0.50/0.73        | ((sk_C_2) = (k1_xboole_0)))),
% 0.50/0.73      inference('sup+', [status(thm)], ['12', '17'])).
% 0.50/0.73  thf(d1_tarski, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.50/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.50/0.73  thf('19', plain,
% 0.50/0.73      (![X32 : $i, X34 : $i, X35 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X35 @ X34)
% 0.50/0.73          | ((X35) = (X32))
% 0.50/0.73          | ((X34) != (k1_tarski @ X32)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_tarski])).
% 0.50/0.73  thf('20', plain,
% 0.50/0.73      (![X32 : $i, X35 : $i]:
% 0.50/0.73         (((X35) = (X32)) | ~ (r2_hidden @ X35 @ (k1_tarski @ X32)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['19'])).
% 0.50/0.73  thf('21', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B @ sk_C_2) = (sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['18', '20'])).
% 0.50/0.74  thf('22', plain,
% 0.50/0.74      (![X15 : $i]:
% 0.50/0.74         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.50/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.50/0.74  thf('23', plain,
% 0.50/0.74      (((r2_hidden @ sk_A @ sk_C_2)
% 0.50/0.74        | ((sk_C_2) = (k1_xboole_0))
% 0.50/0.74        | ((sk_C_2) = (k1_xboole_0)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['21', '22'])).
% 0.50/0.74  thf('24', plain,
% 0.50/0.74      ((((sk_C_2) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_C_2))),
% 0.50/0.74      inference('simplify', [status(thm)], ['23'])).
% 0.50/0.74  thf('25', plain,
% 0.50/0.74      (![X1 : $i, X3 : $i]:
% 0.50/0.74         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.74  thf('26', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('27', plain,
% 0.50/0.74      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.50/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.50/0.74  thf('28', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.50/0.74      inference('sup+', [status(thm)], ['26', '27'])).
% 0.50/0.74  thf('29', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.74          | (r2_hidden @ X0 @ X2)
% 0.50/0.74          | ~ (r1_tarski @ X1 @ X2))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.74  thf('30', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.74  thf('31', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((r1_tarski @ sk_B_1 @ X0)
% 0.50/0.74          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['25', '30'])).
% 0.50/0.74  thf('32', plain,
% 0.50/0.74      (![X32 : $i, X35 : $i]:
% 0.50/0.74         (((X35) = (X32)) | ~ (r2_hidden @ X35 @ (k1_tarski @ X32)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['19'])).
% 0.50/0.74  thf('33', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((r1_tarski @ sk_B_1 @ X0) | ((sk_C @ X0 @ sk_B_1) = (sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.74  thf('34', plain,
% 0.50/0.74      (![X1 : $i, X3 : $i]:
% 0.50/0.74         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.74  thf('35', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (r2_hidden @ sk_A @ X0)
% 0.50/0.74          | (r1_tarski @ sk_B_1 @ X0)
% 0.50/0.74          | (r1_tarski @ sk_B_1 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.74  thf('36', plain,
% 0.50/0.74      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.50/0.74      inference('simplify', [status(thm)], ['35'])).
% 0.50/0.74  thf('37', plain,
% 0.50/0.74      ((((sk_C_2) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.50/0.74      inference('sup-', [status(thm)], ['24', '36'])).
% 0.50/0.74  thf('38', plain,
% 0.50/0.74      (![X20 : $i, X21 : $i]:
% 0.50/0.74         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 0.50/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.74  thf('39', plain,
% 0.50/0.74      ((((sk_C_2) = (k1_xboole_0))
% 0.50/0.74        | ((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.74  thf('40', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('41', plain,
% 0.50/0.74      ((((k1_tarski @ sk_A) = (sk_C_2)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['39', '40'])).
% 0.50/0.74  thf('42', plain,
% 0.50/0.74      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.50/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('split', [status(esa)], ['0'])).
% 0.50/0.74  thf('43', plain,
% 0.50/0.74      (((((sk_C_2) != (sk_C_2)) | ((sk_C_2) = (k1_xboole_0))))
% 0.50/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.50/0.74  thf('44', plain,
% 0.50/0.74      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.74  thf(t95_xboole_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( k3_xboole_0 @ A @ B ) =
% 0.50/0.74       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.50/0.74  thf('45', plain,
% 0.50/0.74      (![X30 : $i, X31 : $i]:
% 0.50/0.74         ((k3_xboole_0 @ X30 @ X31)
% 0.50/0.74           = (k5_xboole_0 @ (k5_xboole_0 @ X30 @ X31) @ 
% 0.50/0.74              (k2_xboole_0 @ X30 @ X31)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.50/0.74  thf(t91_xboole_1, axiom,
% 0.50/0.74    (![A:$i,B:$i,C:$i]:
% 0.50/0.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.50/0.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.50/0.74  thf('46', plain,
% 0.50/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 0.50/0.74           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.74  thf('47', plain,
% 0.50/0.74      (![X30 : $i, X31 : $i]:
% 0.50/0.74         ((k3_xboole_0 @ X30 @ X31)
% 0.50/0.74           = (k5_xboole_0 @ X30 @ 
% 0.50/0.74              (k5_xboole_0 @ X31 @ (k2_xboole_0 @ X30 @ X31))))),
% 0.50/0.74      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.74  thf(t92_xboole_1, axiom,
% 0.50/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.50/0.74  thf('48', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 0.50/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.74  thf('49', plain,
% 0.50/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 0.50/0.74           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.50/0.74  thf('50', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.74           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['48', '49'])).
% 0.50/0.74  thf('51', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 0.50/0.74           = (k3_xboole_0 @ X0 @ X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['47', '50'])).
% 0.50/0.74  thf(idempotence_k2_xboole_0, axiom,
% 0.50/0.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.50/0.74  thf('52', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ X13) = (X13))),
% 0.50/0.74      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.50/0.74  thf(idempotence_k3_xboole_0, axiom,
% 0.50/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.50/0.74  thf('53', plain, (![X14 : $i]: ((k3_xboole_0 @ X14 @ X14) = (X14))),
% 0.50/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.50/0.74  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.50/0.74  thf('55', plain,
% 0.50/0.74      ((![X0 : $i]: ((k5_xboole_0 @ sk_C_2 @ X0) = (X0)))
% 0.50/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('sup+', [status(thm)], ['44', '54'])).
% 0.50/0.74  thf('56', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('57', plain,
% 0.50/0.74      (![X30 : $i, X31 : $i]:
% 0.50/0.74         ((k3_xboole_0 @ X30 @ X31)
% 0.50/0.74           = (k5_xboole_0 @ X30 @ 
% 0.50/0.74              (k5_xboole_0 @ X31 @ (k2_xboole_0 @ X30 @ X31))))),
% 0.50/0.74      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.74  thf('58', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.50/0.74           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['48', '49'])).
% 0.50/0.74  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.50/0.74  thf('60', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('demod', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('61', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.50/0.74           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['57', '60'])).
% 0.50/0.74  thf(t100_xboole_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.74  thf('62', plain,
% 0.50/0.74      (![X16 : $i, X17 : $i]:
% 0.50/0.74         ((k4_xboole_0 @ X16 @ X17)
% 0.50/0.74           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.74  thf('63', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.50/0.74           = (k4_xboole_0 @ X1 @ X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['61', '62'])).
% 0.50/0.74  thf('64', plain,
% 0.50/0.74      (((k5_xboole_0 @ sk_C_2 @ (k1_tarski @ sk_A))
% 0.50/0.74         = (k4_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.50/0.74      inference('sup+', [status(thm)], ['56', '63'])).
% 0.50/0.74  thf('65', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('demod', [status(thm)], ['58', '59'])).
% 0.50/0.74  thf('66', plain,
% 0.50/0.74      (((k1_tarski @ sk_A)
% 0.50/0.74         = (k5_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['64', '65'])).
% 0.50/0.74  thf('67', plain,
% 0.50/0.74      ((((k1_tarski @ sk_A) = (k4_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.50/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('sup+', [status(thm)], ['55', '66'])).
% 0.50/0.74  thf('68', plain,
% 0.50/0.74      ((((sk_C_2) != (k4_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.50/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('demod', [status(thm)], ['1', '67'])).
% 0.50/0.74  thf('69', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.50/0.74      inference('sup+', [status(thm)], ['26', '27'])).
% 0.50/0.74  thf(d8_xboole_0, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.50/0.74       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.50/0.74  thf('70', plain,
% 0.50/0.74      (![X10 : $i, X12 : $i]:
% 0.50/0.74         ((r2_xboole_0 @ X10 @ X12)
% 0.50/0.74          | ((X10) = (X12))
% 0.50/0.74          | ~ (r1_tarski @ X10 @ X12))),
% 0.50/0.74      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.50/0.74  thf('71', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_tarski @ sk_A))
% 0.50/0.74        | (r2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['69', '70'])).
% 0.50/0.74  thf('72', plain,
% 0.50/0.74      (![X15 : $i]:
% 0.50/0.74         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.50/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.50/0.74  thf('73', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((r2_hidden @ X0 @ (k1_tarski @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.50/0.74  thf('74', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_xboole_0))
% 0.50/0.74        | (r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['72', '73'])).
% 0.50/0.74  thf('75', plain,
% 0.50/0.74      (![X32 : $i, X35 : $i]:
% 0.50/0.74         (((X35) = (X32)) | ~ (r2_hidden @ X35 @ (k1_tarski @ X32)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['19'])).
% 0.50/0.74  thf('76', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['74', '75'])).
% 0.50/0.74  thf('77', plain,
% 0.50/0.74      (![X15 : $i]:
% 0.50/0.74         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 0.50/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.50/0.74  thf('78', plain,
% 0.50/0.74      (((r2_hidden @ sk_A @ sk_B_1)
% 0.50/0.74        | ((sk_B_1) = (k1_xboole_0))
% 0.50/0.74        | ((sk_B_1) = (k1_xboole_0)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['76', '77'])).
% 0.50/0.74  thf('79', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.50/0.74      inference('simplify', [status(thm)], ['78'])).
% 0.50/0.74  thf('80', plain,
% 0.50/0.74      (![X1 : $i, X3 : $i]:
% 0.50/0.74         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.74  thf('81', plain,
% 0.50/0.74      (![X32 : $i, X35 : $i]:
% 0.50/0.74         (((X35) = (X32)) | ~ (r2_hidden @ X35 @ (k1_tarski @ X32)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['19'])).
% 0.50/0.74  thf('82', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.50/0.74          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['80', '81'])).
% 0.50/0.74  thf('83', plain,
% 0.50/0.74      (![X1 : $i, X3 : $i]:
% 0.50/0.74         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.50/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.74  thf('84', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.74          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.50/0.74          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['82', '83'])).
% 0.50/0.74  thf('85', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.50/0.74      inference('simplify', [status(thm)], ['84'])).
% 0.50/0.74  thf('86', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['79', '85'])).
% 0.50/0.74  thf('87', plain,
% 0.50/0.74      (![X20 : $i, X21 : $i]:
% 0.50/0.74         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 0.50/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.74  thf('88', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_xboole_0))
% 0.50/0.74        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['86', '87'])).
% 0.50/0.74  thf('89', plain,
% 0.50/0.74      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.50/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.50/0.74  thf('90', plain,
% 0.50/0.74      (![X20 : $i, X21 : $i]:
% 0.50/0.74         (((k2_xboole_0 @ X21 @ X20) = (X20)) | ~ (r1_tarski @ X21 @ X20))),
% 0.50/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.74  thf('91', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.50/0.74           = (k2_xboole_0 @ X1 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['89', '90'])).
% 0.50/0.74  thf('92', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.50/0.74           = (k4_xboole_0 @ X1 @ X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['61', '62'])).
% 0.50/0.74  thf('93', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 0.50/0.74           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('sup+', [status(thm)], ['91', '92'])).
% 0.50/0.74  thf('94', plain, (![X14 : $i]: ((k3_xboole_0 @ X14 @ X14) = (X14))),
% 0.50/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.50/0.74  thf('95', plain,
% 0.50/0.74      (![X16 : $i, X17 : $i]:
% 0.50/0.74         ((k4_xboole_0 @ X16 @ X17)
% 0.50/0.74           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.74  thf('96', plain,
% 0.50/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['94', '95'])).
% 0.50/0.74  thf('97', plain,
% 0.50/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['94', '95'])).
% 0.50/0.74  thf('98', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 0.50/0.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.50/0.74  thf('99', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['97', '98'])).
% 0.50/0.74  thf('100', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.50/0.74      inference('demod', [status(thm)], ['93', '96', '99'])).
% 0.50/0.74  thf(t105_xboole_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.50/0.74          ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.74  thf('101', plain,
% 0.50/0.74      (![X18 : $i, X19 : $i]:
% 0.50/0.74         (~ (r2_xboole_0 @ X18 @ X19)
% 0.50/0.74          | ((k4_xboole_0 @ X19 @ X18) != (k1_xboole_0)))),
% 0.50/0.74      inference('cnf', [status(esa)], [t105_xboole_1])).
% 0.50/0.74  thf('102', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (((k1_xboole_0) != (k1_xboole_0))
% 0.50/0.74          | ~ (r2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 0.50/0.74      inference('sup-', [status(thm)], ['100', '101'])).
% 0.50/0.74  thf('103', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]: ~ (r2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)),
% 0.50/0.74      inference('simplify', [status(thm)], ['102'])).
% 0.50/0.74  thf('104', plain,
% 0.50/0.74      ((~ (r2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.50/0.74        | ((sk_B_1) = (k1_xboole_0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['88', '103'])).
% 0.50/0.74  thf('105', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_tarski @ sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['71', '104'])).
% 0.50/0.74  thf('106', plain,
% 0.50/0.74      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('107', plain,
% 0.50/0.74      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.50/0.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('split', [status(esa)], ['106'])).
% 0.50/0.74  thf('108', plain,
% 0.50/0.74      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.50/0.74         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['105', '107'])).
% 0.50/0.74  thf('109', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['108'])).
% 0.50/0.74  thf('110', plain,
% 0.50/0.74      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.74  thf('111', plain,
% 0.50/0.74      ((((sk_C_2) = (sk_B_1)))
% 0.50/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.50/0.74             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('sup+', [status(thm)], ['109', '110'])).
% 0.50/0.74  thf('112', plain,
% 0.50/0.74      (~ (((sk_B_1) = (k1_tarski @ sk_A))) | ~ (((sk_C_2) = (k1_xboole_0)))),
% 0.50/0.74      inference('split', [status(esa)], ['106'])).
% 0.50/0.74  thf('113', plain,
% 0.50/0.74      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('114', plain,
% 0.50/0.74      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.50/0.74       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('split', [status(esa)], ['113'])).
% 0.50/0.74  thf('115', plain,
% 0.50/0.74      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.74  thf('116', plain,
% 0.50/0.74      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.50/0.74      inference('split', [status(esa)], ['106'])).
% 0.50/0.74  thf('117', plain,
% 0.50/0.74      ((((sk_C_2) != (sk_C_2)))
% 0.50/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))) & 
% 0.50/0.74             ~ (((sk_C_2) = (k1_xboole_0))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['115', '116'])).
% 0.50/0.74  thf('118', plain,
% 0.50/0.74      ((((sk_C_2) = (k1_xboole_0))) | (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['117'])).
% 0.50/0.74  thf('119', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['108'])).
% 0.50/0.74  thf('120', plain,
% 0.50/0.74      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.50/0.74      inference('split', [status(esa)], ['0'])).
% 0.50/0.74  thf('121', plain,
% 0.50/0.74      ((((sk_B_1) != (sk_B_1)))
% 0.50/0.74         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.50/0.74             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('sup-', [status(thm)], ['119', '120'])).
% 0.50/0.74  thf('122', plain,
% 0.50/0.74      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('simplify', [status(thm)], ['121'])).
% 0.50/0.74  thf('123', plain,
% 0.50/0.74      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.50/0.74      inference('split', [status(esa)], ['0'])).
% 0.50/0.74  thf('124', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('sat_resolution*', [status(thm)],
% 0.50/0.74                ['112', '114', '118', '122', '123'])).
% 0.50/0.74  thf('125', plain, (~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('sat_resolution*', [status(thm)], ['112', '114', '118'])).
% 0.50/0.74  thf('126', plain, (((sk_C_2) = (sk_B_1))),
% 0.50/0.74      inference('simpl_trail', [status(thm)], ['111', '124', '125'])).
% 0.50/0.74  thf('127', plain, (((sk_C_2) = (sk_B_1))),
% 0.50/0.74      inference('simpl_trail', [status(thm)], ['111', '124', '125'])).
% 0.50/0.74  thf('128', plain,
% 0.50/0.74      ((((sk_C_2) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.74  thf('129', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['97', '98'])).
% 0.50/0.74  thf('130', plain,
% 0.50/0.74      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (sk_C_2)))
% 0.50/0.74         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('sup+', [status(thm)], ['128', '129'])).
% 0.50/0.74  thf('131', plain, (((sk_C_2) = (sk_B_1))),
% 0.50/0.74      inference('simpl_trail', [status(thm)], ['111', '124', '125'])).
% 0.50/0.74  thf('132', plain,
% 0.50/0.74      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('demod', [status(thm)], ['68', '126', '127', '130', '131'])).
% 0.50/0.74  thf('133', plain, (($false) <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.50/0.74      inference('simplify', [status(thm)], ['132'])).
% 0.50/0.74  thf('134', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.50/0.74      inference('sat_resolution*', [status(thm)],
% 0.50/0.74                ['112', '114', '118', '122', '123'])).
% 0.50/0.74  thf('135', plain, ($false),
% 0.50/0.74      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 0.50/0.74  
% 0.50/0.74  % SZS output end Refutation
% 0.50/0.74  
% 0.60/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
