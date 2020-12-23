%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vefJ1rWjIm

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:28 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 661 expanded)
%              Number of leaves         :   31 ( 190 expanded)
%              Depth                    :   23
%              Number of atoms          : 1089 (7678 expanded)
%              Number of equality atoms :  196 (1574 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X61
        = ( k1_tarski @ X60 ) )
      | ( X61 = k1_xboole_0 )
      | ~ ( r1_tarski @ X61 @ ( k1_tarski @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','22'])).

thf('24',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X61: $i,X62: $i] :
      ( ( r1_tarski @ X61 @ ( k1_tarski @ X62 ) )
      | ( X61 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('47',plain,(
    ! [X62: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X62 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('51',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('52',plain,(
    ! [X26: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X28 )
      | ( X30 = X29 )
      | ( X30 = X26 )
      | ( X28
       != ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('53',plain,(
    ! [X26: $i,X29: $i,X30: $i] :
      ( ( X30 = X26 )
      | ( X30 = X29 )
      | ~ ( r2_hidden @ X30 @ ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_B @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_B @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 != X0 )
        | ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('64',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('70',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('71',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf('74',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('75',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['62','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('80',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('81',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('90',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('91',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('93',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','97'])).

thf('99',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','100'])).

thf('102',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('104',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('105',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ) ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_1 @ sk_B_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('109',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 ) ),
    inference(simplify,[status(thm)],['109'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('111',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('112',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,
    ( ( sk_C_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('119',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('120',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['118','119'])).

thf('121',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('122',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['117','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','122'])).

thf('124',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['24','123'])).

thf('125',plain,(
    $false ),
    inference(simplify,[status(thm)],['124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vefJ1rWjIm
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 1090 iterations in 0.517s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i > $i).
% 0.75/0.98  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.75/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.98  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.75/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(t43_zfmisc_1, conjecture,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.75/0.98          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.75/0.98          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.75/0.98          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.98        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.75/0.98             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.75/0.98             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.75/0.98             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.75/0.98  thf('0', plain,
% 0.75/0.98      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('1', plain,
% 0.75/0.98      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.75/0.98         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('split', [status(esa)], ['0'])).
% 0.75/0.98  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      ((((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.75/0.98         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('demod', [status(thm)], ['1', '2'])).
% 0.75/0.98  thf('4', plain,
% 0.75/0.98      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('split', [status(esa)], ['0'])).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.75/0.98       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('split', [status(esa)], ['5'])).
% 0.75/0.98  thf(t7_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.98  thf('7', plain,
% 0.75/0.98      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.75/0.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.98  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(l3_zfmisc_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.75/0.98       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X60 : $i, X61 : $i]:
% 0.75/0.98         (((X61) = (k1_tarski @ X60))
% 0.75/0.98          | ((X61) = (k1_xboole_0))
% 0.75/0.98          | ~ (r1_tarski @ X61 @ (k1_tarski @ X60)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98          | ((X0) = (k1_xboole_0))
% 0.75/0.98          | ((X0) = (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.98  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('12', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98          | ((X0) = (k1_xboole_0))
% 0.75/0.98          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '12'])).
% 0.75/0.98  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.75/0.98         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('split', [status(esa)], ['15'])).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.75/0.98         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['14', '16'])).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.75/0.98         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['13', '17'])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('simplify', [status(thm)], ['18'])).
% 0.75/0.98  thf('20', plain,
% 0.75/0.98      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.75/0.98      inference('split', [status(esa)], ['0'])).
% 0.75/0.98  thf('21', plain,
% 0.75/0.98      ((((sk_B_1) != (sk_B_1)))
% 0.75/0.98         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.75/0.98             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['21'])).
% 0.75/0.98  thf('23', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 0.75/0.98  thf('24', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.75/0.98  thf(idempotence_k2_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.75/0.98  thf('25', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 0.75/0.98      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.75/0.98  thf(t95_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k3_xboole_0 @ A @ B ) =
% 0.75/0.98       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      (![X24 : $i, X25 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X24 @ X25)
% 0.75/0.98           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 0.75/0.98              (k2_xboole_0 @ X24 @ X25)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.75/0.98  thf(t91_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.98       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.75/0.98           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.98  thf('28', plain,
% 0.75/0.98      (![X24 : $i, X25 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X24 @ X25)
% 0.75/0.98           = (k5_xboole_0 @ X24 @ 
% 0.75/0.98              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.75/0.98      inference('demod', [status(thm)], ['26', '27'])).
% 0.75/0.98  thf('29', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X0 @ X0)
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['25', '28'])).
% 0.75/0.98  thf(idempotence_k3_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.75/0.98  thf('30', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.75/0.98      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.75/0.98  thf(t92_xboole_1, axiom,
% 0.75/0.98    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.75/0.98  thf('31', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.75/0.98  thf('32', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.98      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.75/0.98  thf(commutativity_k5_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.98  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['32', '33'])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      (![X24 : $i, X25 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X24 @ X25)
% 0.75/0.98           = (k5_xboole_0 @ X24 @ 
% 0.75/0.98              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.75/0.98      inference('demod', [status(thm)], ['26', '27'])).
% 0.75/0.98  thf('36', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['34', '35'])).
% 0.75/0.98  thf(d3_tarski, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( r1_tarski @ A @ B ) <=>
% 0.75/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/0.98  thf('37', plain,
% 0.75/0.98      (![X6 : $i, X8 : $i]:
% 0.75/0.98         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf(d1_xboole_0, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.75/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/0.98  thf(t12_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      (![X14 : $i, X15 : $i]:
% 0.75/0.98         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.75/0.98      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.98  thf('42', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.98           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['34', '35'])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ X0))
% 0.75/0.98          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['41', '42'])).
% 0.75/0.98  thf('44', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.75/0.98  thf('45', plain,
% 0.75/0.98      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.75/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.75/0.98  thf('46', plain,
% 0.75/0.98      (![X61 : $i, X62 : $i]:
% 0.75/0.98         ((r1_tarski @ X61 @ (k1_tarski @ X62)) | ((X61) != (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      (![X62 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X62))),
% 0.75/0.98      inference('simplify', [status(thm)], ['46'])).
% 0.75/0.98  thf('48', plain,
% 0.75/0.98      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X5 @ X6)
% 0.75/0.98          | (r2_hidden @ X5 @ X7)
% 0.75/0.98          | ~ (r1_tarski @ X6 @ X7))),
% 0.75/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.98  thf('49', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.98          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['47', '48'])).
% 0.75/0.98  thf('50', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((v1_xboole_0 @ k1_xboole_0)
% 0.75/0.98          | (r2_hidden @ (sk_B @ k1_xboole_0) @ (k1_tarski @ X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['45', '49'])).
% 0.75/0.98  thf(t69_enumset1, axiom,
% 0.75/0.98    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.98  thf('51', plain,
% 0.75/0.98      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.75/0.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.98  thf(d2_tarski, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.75/0.98       ( ![D:$i]:
% 0.75/0.98         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      (![X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X30 @ X28)
% 0.75/0.98          | ((X30) = (X29))
% 0.75/0.98          | ((X30) = (X26))
% 0.75/0.98          | ((X28) != (k2_tarski @ X29 @ X26)))),
% 0.75/0.98      inference('cnf', [status(esa)], [d2_tarski])).
% 0.75/0.98  thf('53', plain,
% 0.75/0.98      (![X26 : $i, X29 : $i, X30 : $i]:
% 0.75/0.98         (((X30) = (X26))
% 0.75/0.98          | ((X30) = (X29))
% 0.75/0.98          | ~ (r2_hidden @ X30 @ (k2_tarski @ X29 @ X26)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['52'])).
% 0.75/0.98  thf('54', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['51', '53'])).
% 0.75/0.98  thf('55', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['54'])).
% 0.75/0.98  thf('56', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((v1_xboole_0 @ k1_xboole_0) | ((sk_B @ k1_xboole_0) = (X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['50', '55'])).
% 0.75/0.98  thf('57', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((v1_xboole_0 @ k1_xboole_0) | ((sk_B @ k1_xboole_0) = (X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['50', '55'])).
% 0.75/0.98  thf('58', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((X0) = (X1))
% 0.75/0.98          | (v1_xboole_0 @ k1_xboole_0)
% 0.75/0.98          | (v1_xboole_0 @ k1_xboole_0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['56', '57'])).
% 0.75/0.98  thf('59', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ((X0) = (X1)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['58'])).
% 0.75/0.98  thf('60', plain,
% 0.75/0.98      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.75/0.98      inference('split', [status(esa)], ['15'])).
% 0.75/0.98  thf('61', plain,
% 0.75/0.98      ((![X0 : $i]: (((sk_C_1) != (X0)) | (v1_xboole_0 @ k1_xboole_0)))
% 0.75/0.98         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['59', '60'])).
% 0.75/0.98  thf('62', plain,
% 0.75/0.98      (((v1_xboole_0 @ k1_xboole_0)) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.75/0.98      inference('simplify', [status(thm)], ['61'])).
% 0.75/0.98  thf('63', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ((X0) = (X1)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['58'])).
% 0.75/0.98  thf('64', plain,
% 0.75/0.98      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.75/0.98         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['14', '16'])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      ((![X0 : $i]: (((sk_B_1) != (X0)) | (v1_xboole_0 @ k1_xboole_0)))
% 0.75/0.98         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['63', '64'])).
% 0.75/0.98  thf('66', plain,
% 0.75/0.98      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('simplify', [status(thm)], ['18'])).
% 0.75/0.98  thf('67', plain,
% 0.75/0.98      ((![X0 : $i]: (((sk_B_1) != (X0)) | (v1_xboole_0 @ sk_B_1)))
% 0.75/0.98         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('demod', [status(thm)], ['65', '66'])).
% 0.75/0.98  thf('68', plain,
% 0.75/0.98      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.75/0.98      inference('simplify', [status(thm)], ['67'])).
% 0.75/0.98  thf('69', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['39', '40'])).
% 0.75/0.98  thf('70', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.75/0.98  thf('71', plain, ((((sk_C_1) != (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['69', '70'])).
% 0.75/0.98  thf('72', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.75/0.98      inference('simplify', [status(thm)], ['71'])).
% 0.75/0.98  thf('73', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['68', '72'])).
% 0.75/0.98  thf('74', plain,
% 0.75/0.98      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('split', [status(esa)], ['15'])).
% 0.75/0.98  thf('75', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.75/0.98  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.75/0.98      inference('simpl_trail', [status(thm)], ['62', '75'])).
% 0.75/0.98  thf('77', plain,
% 0.75/0.98      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.75/0.98      inference('demod', [status(thm)], ['43', '44', '76'])).
% 0.75/0.98  thf('78', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['36', '77'])).
% 0.75/0.98  thf('79', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.98  thf('80', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.75/0.98  thf('81', plain,
% 0.75/0.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.75/0.98           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.75/0.98  thf('82', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.98           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['80', '81'])).
% 0.75/0.98  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['32', '33'])).
% 0.75/0.98  thf('84', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['82', '83'])).
% 0.75/0.98  thf('85', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['79', '84'])).
% 0.75/0.98  thf('86', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((X0) = (k5_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['78', '85'])).
% 0.75/0.98  thf('87', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.98      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.75/0.98  thf('88', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['86', '87'])).
% 0.75/0.98  thf('89', plain,
% 0.75/0.98      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '12'])).
% 0.75/0.98  thf('90', plain,
% 0.75/0.98      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '12'])).
% 0.75/0.98  thf('91', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('92', plain,
% 0.75/0.98      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.75/0.98      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.98  thf(l51_zfmisc_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.98  thf('93', plain,
% 0.75/0.98      (![X63 : $i, X64 : $i]:
% 0.75/0.98         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 0.75/0.98      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.75/0.98  thf('94', plain,
% 0.75/0.98      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['92', '93'])).
% 0.75/0.98  thf('95', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 0.75/0.98      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.75/0.98  thf('96', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['94', '95'])).
% 0.75/0.98  thf('97', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 0.75/0.98      inference('sup+', [status(thm)], ['91', '96'])).
% 0.75/0.98  thf('98', plain,
% 0.75/0.98      ((((k3_tarski @ sk_B_1) = (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['90', '97'])).
% 0.75/0.98  thf('99', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('100', plain,
% 0.75/0.98      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['98', '99'])).
% 0.75/0.98  thf('101', plain,
% 0.75/0.98      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['89', '100'])).
% 0.75/0.98  thf('102', plain,
% 0.75/0.98      ((((sk_B_1) = (k1_xboole_0))
% 0.75/0.98        | ((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['101'])).
% 0.75/0.98  thf('103', plain,
% 0.75/0.98      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['98', '99'])).
% 0.75/0.98  thf('104', plain,
% 0.75/0.98      (![X24 : $i, X25 : $i]:
% 0.75/0.98         ((k3_xboole_0 @ X24 @ X25)
% 0.75/0.98           = (k5_xboole_0 @ X24 @ 
% 0.75/0.98              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 0.75/0.98      inference('demod', [status(thm)], ['26', '27'])).
% 0.75/0.98  thf('105', plain,
% 0.75/0.98      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 0.75/0.98          = (k5_xboole_0 @ sk_B_1 @ 
% 0.75/0.98             (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ (k3_tarski @ sk_B_1)))))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['103', '104'])).
% 0.75/0.98  thf('106', plain,
% 0.75/0.98      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 0.75/0.98          = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_1 @ sk_B_1)))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['102', '105'])).
% 0.75/0.98  thf('107', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.98  thf('108', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['82', '83'])).
% 0.75/0.98  thf('109', plain,
% 0.75/0.98      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.75/0.98  thf('110', plain,
% 0.75/0.98      ((((sk_B_1) = (k1_xboole_0))
% 0.75/0.98        | ((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['109'])).
% 0.75/0.98  thf(t17_xboole_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.75/0.98  thf('111', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.75/0.98      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.98  thf('112', plain,
% 0.75/0.98      (((r1_tarski @ sk_C_1 @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['110', '111'])).
% 0.75/0.98  thf('113', plain,
% 0.75/0.98      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '12'])).
% 0.75/0.98  thf('114', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98          | ((X0) = (k1_xboole_0))
% 0.75/0.98          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf('115', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X0 @ sk_B_1)
% 0.75/0.98          | ((sk_B_1) = (k1_xboole_0))
% 0.75/0.98          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98          | ((X0) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['113', '114'])).
% 0.75/0.98  thf('116', plain,
% 0.75/0.98      ((((sk_B_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_C_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['112', '115'])).
% 0.75/0.98  thf('117', plain,
% 0.75/0.98      ((((sk_C_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.75/0.98        | ((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['116'])).
% 0.75/0.98  thf('118', plain,
% 0.75/0.98      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.75/0.98      inference('split', [status(esa)], ['15'])).
% 0.75/0.98  thf('119', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.75/0.98  thf('120', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.75/0.98      inference('simpl_trail', [status(thm)], ['118', '119'])).
% 0.75/0.98  thf('121', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.75/0.98      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.75/0.98  thf('122', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.75/0.98      inference('simplify_reflect-', [status(thm)], ['117', '120', '121'])).
% 0.75/0.98  thf('123', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B_1 @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['88', '122'])).
% 0.75/0.98  thf('124', plain, (((sk_C_1) != (sk_C_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['24', '123'])).
% 0.75/0.98  thf('125', plain, ($false), inference('simplify', [status(thm)], ['124'])).
% 0.75/0.98  
% 0.75/0.98  % SZS output end Refutation
% 0.75/0.98  
% 0.75/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
