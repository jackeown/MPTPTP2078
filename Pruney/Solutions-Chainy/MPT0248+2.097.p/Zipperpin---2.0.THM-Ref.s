%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lvm258Bqtm

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:32 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 322 expanded)
%              Number of leaves         :   24 (  91 expanded)
%              Depth                    :   34
%              Number of atoms          : 1011 (3726 expanded)
%              Number of equality atoms :  183 ( 797 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( X25 = X22 )
      | ( X24
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25 = X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_tarski @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('11',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','17'])).

thf('19',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('24',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('29',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('30',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38
        = ( k1_tarski @ X37 ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('31',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('33',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('35',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ X0 @ X0 )
        = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( k1_tarski @ sk_A )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('42',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('44',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
      | ( sk_C_1 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25 = X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_tarski @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('46',plain,
    ( ( ( sk_C_1 = sk_B_1 )
      | ( ( sk_B @ sk_C_1 )
        = sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('48',plain,
    ( ( ( r2_hidden @ sk_A @ sk_C_1 )
      | ( sk_C_1 = sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('50',plain,
    ( ( ( r2_hidden @ sk_A @ sk_C_1 )
      | ( sk_C_1 = sk_B_1 )
      | ( sk_C_1 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( sk_C_1 = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 = sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_C_1 )
      | ( sk_C_1 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','53'])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('56',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('57',plain,
    ( ( ( sk_C_1 = sk_B_1 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      | ( sk_C_1 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      | ( sk_C_1 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('60',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ ( k1_tarski @ X39 ) )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('61',plain,(
    ! [X39: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','63'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('66',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
        | ( r1_tarski @ sk_B_1 @ X1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( sk_C_1 = sk_B_1 )
      | ( r1_tarski @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('69',plain,
    ( ( ( sk_C_1 = sk_B_1 )
      | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
        = sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = sk_C_1 )
      | ( sk_C_1 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','69'])).

thf('71',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('74',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('77',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('78',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['73','75','79'])).

thf('81',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['72','80'])).

thf('82',plain,
    ( ( sk_C_1 = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','81'])).

thf('83',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('86',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('87',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43 != X42 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ ( k1_tarski @ X42 ) )
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('88',plain,(
    ! [X42: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X42 ) @ ( k1_tarski @ X42 ) )
     != ( k1_tarski @ X42 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('90',plain,(
    ! [X42: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X42 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_xboole_0 != sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('93',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('96',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','96'])).

thf('98',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['19','97'])).

thf('99',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('101',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('106',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['0','106'])).

thf('108',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['72','80'])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lvm258Bqtm
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:46:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.64/1.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.64/1.87  % Solved by: fo/fo7.sh
% 1.64/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.87  % done 2420 iterations in 1.380s
% 1.64/1.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.64/1.87  % SZS output start Refutation
% 1.64/1.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.64/1.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.64/1.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.64/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.64/1.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.64/1.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.64/1.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.64/1.87  thf(sk_B_type, type, sk_B: $i > $i).
% 1.64/1.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.64/1.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.64/1.87  thf(t43_zfmisc_1, conjecture,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.64/1.87          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.64/1.87          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.64/1.87          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.64/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.87    (~( ![A:$i,B:$i,C:$i]:
% 1.64/1.87        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.64/1.87             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.64/1.87             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.64/1.87             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.64/1.87    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.64/1.87  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(t7_xboole_0, axiom,
% 1.64/1.87    (![A:$i]:
% 1.64/1.87     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.64/1.87          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.64/1.87  thf('2', plain,
% 1.64/1.87      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.64/1.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.64/1.87  thf(d3_xboole_0, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.64/1.87       ( ![D:$i]:
% 1.64/1.87         ( ( r2_hidden @ D @ C ) <=>
% 1.64/1.87           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.64/1.87  thf('3', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X0 @ X1)
% 1.64/1.87          | (r2_hidden @ X0 @ X2)
% 1.64/1.87          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.64/1.87  thf('4', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.64/1.87         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.64/1.87      inference('simplify', [status(thm)], ['3'])).
% 1.64/1.87  thf('5', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         (((X0) = (k1_xboole_0))
% 1.64/1.87          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['2', '4'])).
% 1.64/1.87  thf('6', plain,
% 1.64/1.87      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 1.64/1.87        | ((sk_C_1) = (k1_xboole_0)))),
% 1.64/1.87      inference('sup+', [status(thm)], ['1', '5'])).
% 1.64/1.87  thf(d1_tarski, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.64/1.87       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.64/1.87  thf('7', plain,
% 1.64/1.87      (![X22 : $i, X24 : $i, X25 : $i]:
% 1.64/1.87         (~ (r2_hidden @ X25 @ X24)
% 1.64/1.87          | ((X25) = (X22))
% 1.64/1.87          | ((X24) != (k1_tarski @ X22)))),
% 1.64/1.87      inference('cnf', [status(esa)], [d1_tarski])).
% 1.64/1.87  thf('8', plain,
% 1.64/1.87      (![X22 : $i, X25 : $i]:
% 1.64/1.87         (((X25) = (X22)) | ~ (r2_hidden @ X25 @ (k1_tarski @ X22)))),
% 1.64/1.87      inference('simplify', [status(thm)], ['7'])).
% 1.64/1.87  thf('9', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['6', '8'])).
% 1.64/1.87  thf('10', plain,
% 1.64/1.87      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.64/1.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.64/1.87  thf('11', plain,
% 1.64/1.87      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.64/1.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.64/1.87  thf(t38_zfmisc_1, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.64/1.87       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.64/1.87  thf('12', plain,
% 1.64/1.87      (![X45 : $i, X47 : $i, X48 : $i]:
% 1.64/1.87         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 1.64/1.87          | ~ (r2_hidden @ X47 @ X48)
% 1.64/1.87          | ~ (r2_hidden @ X45 @ X48))),
% 1.64/1.87      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.64/1.87  thf('13', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         (((X0) = (k1_xboole_0))
% 1.64/1.87          | ~ (r2_hidden @ X1 @ X0)
% 1.64/1.87          | (r1_tarski @ (k2_tarski @ X1 @ (sk_B @ X0)) @ X0))),
% 1.64/1.87      inference('sup-', [status(thm)], ['11', '12'])).
% 1.64/1.87  thf('14', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         (((X0) = (k1_xboole_0))
% 1.64/1.87          | (r1_tarski @ (k2_tarski @ (sk_B @ X0) @ (sk_B @ X0)) @ X0)
% 1.64/1.87          | ((X0) = (k1_xboole_0)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['10', '13'])).
% 1.64/1.87  thf(t69_enumset1, axiom,
% 1.64/1.87    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.64/1.87  thf('15', plain,
% 1.64/1.87      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 1.64/1.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.64/1.87  thf('16', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         (((X0) = (k1_xboole_0))
% 1.64/1.87          | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 1.64/1.87          | ((X0) = (k1_xboole_0)))),
% 1.64/1.87      inference('demod', [status(thm)], ['14', '15'])).
% 1.64/1.87  thf('17', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         ((r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0) | ((X0) = (k1_xboole_0)))),
% 1.64/1.87      inference('simplify', [status(thm)], ['16'])).
% 1.64/1.87  thf('18', plain,
% 1.64/1.87      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)
% 1.64/1.87        | ((sk_C_1) = (k1_xboole_0))
% 1.64/1.87        | ((sk_C_1) = (k1_xboole_0)))),
% 1.64/1.87      inference('sup+', [status(thm)], ['9', '17'])).
% 1.64/1.87  thf('19', plain,
% 1.64/1.87      ((((sk_C_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1))),
% 1.64/1.87      inference('simplify', [status(thm)], ['18'])).
% 1.64/1.87  thf('20', plain,
% 1.64/1.87      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('21', plain,
% 1.64/1.87      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.64/1.87      inference('split', [status(esa)], ['20'])).
% 1.64/1.87  thf('22', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('23', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['6', '8'])).
% 1.64/1.87  thf('24', plain,
% 1.64/1.87      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.64/1.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.64/1.87  thf('25', plain,
% 1.64/1.87      (((r2_hidden @ sk_A @ sk_C_1)
% 1.64/1.87        | ((sk_C_1) = (k1_xboole_0))
% 1.64/1.87        | ((sk_C_1) = (k1_xboole_0)))),
% 1.64/1.87      inference('sup+', [status(thm)], ['23', '24'])).
% 1.64/1.87  thf('26', plain,
% 1.64/1.87      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ sk_C_1))),
% 1.64/1.87      inference('simplify', [status(thm)], ['25'])).
% 1.64/1.87  thf('27', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf(t7_xboole_1, axiom,
% 1.64/1.87    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.64/1.87  thf('28', plain,
% 1.64/1.87      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.64/1.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.64/1.87  thf('29', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.64/1.87      inference('sup+', [status(thm)], ['27', '28'])).
% 1.64/1.87  thf(l3_zfmisc_1, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.64/1.87       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.64/1.87  thf('30', plain,
% 1.64/1.87      (![X37 : $i, X38 : $i]:
% 1.64/1.87         (((X38) = (k1_tarski @ X37))
% 1.64/1.87          | ((X38) = (k1_xboole_0))
% 1.64/1.87          | ~ (r1_tarski @ X38 @ (k1_tarski @ X37)))),
% 1.64/1.87      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.64/1.87  thf('31', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['29', '30'])).
% 1.64/1.87  thf('32', plain,
% 1.64/1.87      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('split', [status(esa)], ['20'])).
% 1.64/1.87  thf('33', plain,
% 1.64/1.87      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['31', '32'])).
% 1.64/1.87  thf('34', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['33'])).
% 1.64/1.87  thf(idempotence_k2_xboole_0, axiom,
% 1.64/1.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.64/1.87  thf('35', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.64/1.87      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.64/1.87  thf(t46_xboole_1, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.64/1.87  thf('36', plain,
% 1.64/1.87      (![X18 : $i, X19 : $i]:
% 1.64/1.87         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 1.64/1.87      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.64/1.87  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.64/1.87      inference('sup+', [status(thm)], ['35', '36'])).
% 1.64/1.87  thf('38', plain,
% 1.64/1.87      ((![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (sk_B_1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup+', [status(thm)], ['34', '37'])).
% 1.64/1.87  thf('39', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('40', plain,
% 1.64/1.87      ((![X0 : $i]:
% 1.64/1.87          ((k1_tarski @ sk_A)
% 1.64/1.87            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ sk_C_1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup+', [status(thm)], ['38', '39'])).
% 1.64/1.87  thf('41', plain,
% 1.64/1.87      (![X0 : $i, X1 : $i]:
% 1.64/1.87         (((X0) = (k1_xboole_0))
% 1.64/1.87          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.64/1.87      inference('sup-', [status(thm)], ['2', '4'])).
% 1.64/1.87  thf('42', plain,
% 1.64/1.87      ((((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 1.64/1.87         | ((sk_C_1) = (k1_xboole_0))))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup+', [status(thm)], ['40', '41'])).
% 1.64/1.87  thf('43', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['33'])).
% 1.64/1.87  thf('44', plain,
% 1.64/1.87      ((((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 1.64/1.87         | ((sk_C_1) = (sk_B_1)))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('demod', [status(thm)], ['42', '43'])).
% 1.64/1.87  thf('45', plain,
% 1.64/1.87      (![X22 : $i, X25 : $i]:
% 1.64/1.87         (((X25) = (X22)) | ~ (r2_hidden @ X25 @ (k1_tarski @ X22)))),
% 1.64/1.87      inference('simplify', [status(thm)], ['7'])).
% 1.64/1.87  thf('46', plain,
% 1.64/1.87      (((((sk_C_1) = (sk_B_1)) | ((sk_B @ sk_C_1) = (sk_A))))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['44', '45'])).
% 1.64/1.87  thf('47', plain,
% 1.64/1.87      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.64/1.87      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.64/1.87  thf('48', plain,
% 1.64/1.87      ((((r2_hidden @ sk_A @ sk_C_1)
% 1.64/1.87         | ((sk_C_1) = (sk_B_1))
% 1.64/1.87         | ((sk_C_1) = (k1_xboole_0))))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup+', [status(thm)], ['46', '47'])).
% 1.64/1.87  thf('49', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['33'])).
% 1.64/1.87  thf('50', plain,
% 1.64/1.87      ((((r2_hidden @ sk_A @ sk_C_1)
% 1.64/1.87         | ((sk_C_1) = (sk_B_1))
% 1.64/1.87         | ((sk_C_1) = (sk_B_1)))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('demod', [status(thm)], ['48', '49'])).
% 1.64/1.87  thf('51', plain,
% 1.64/1.87      (((((sk_C_1) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_C_1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['50'])).
% 1.64/1.87  thf('52', plain,
% 1.64/1.87      (![X45 : $i, X47 : $i, X48 : $i]:
% 1.64/1.87         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 1.64/1.87          | ~ (r2_hidden @ X47 @ X48)
% 1.64/1.87          | ~ (r2_hidden @ X45 @ X48))),
% 1.64/1.87      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.64/1.87  thf('53', plain,
% 1.64/1.87      ((![X0 : $i]:
% 1.64/1.87          (((sk_C_1) = (sk_B_1))
% 1.64/1.87           | ~ (r2_hidden @ X0 @ sk_C_1)
% 1.64/1.87           | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_C_1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['51', '52'])).
% 1.64/1.87  thf('54', plain,
% 1.64/1.87      (((((sk_C_1) = (k1_xboole_0))
% 1.64/1.87         | (r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_C_1)
% 1.64/1.87         | ((sk_C_1) = (sk_B_1)))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['26', '53'])).
% 1.64/1.87  thf('55', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['33'])).
% 1.64/1.87  thf('56', plain,
% 1.64/1.87      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 1.64/1.87      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.64/1.87  thf('57', plain,
% 1.64/1.87      (((((sk_C_1) = (sk_B_1))
% 1.64/1.87         | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)
% 1.64/1.87         | ((sk_C_1) = (sk_B_1)))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('demod', [status(thm)], ['54', '55', '56'])).
% 1.64/1.87  thf('58', plain,
% 1.64/1.87      ((((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1) | ((sk_C_1) = (sk_B_1))))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['57'])).
% 1.64/1.87  thf('59', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['33'])).
% 1.64/1.87  thf('60', plain,
% 1.64/1.87      (![X38 : $i, X39 : $i]:
% 1.64/1.87         ((r1_tarski @ X38 @ (k1_tarski @ X39)) | ((X38) != (k1_xboole_0)))),
% 1.64/1.87      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.64/1.87  thf('61', plain,
% 1.64/1.87      (![X39 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X39))),
% 1.64/1.87      inference('simplify', [status(thm)], ['60'])).
% 1.64/1.87  thf(t12_xboole_1, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.64/1.87  thf('62', plain,
% 1.64/1.87      (![X16 : $i, X17 : $i]:
% 1.64/1.87         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 1.64/1.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.64/1.87  thf('63', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 1.64/1.87      inference('sup-', [status(thm)], ['61', '62'])).
% 1.64/1.87  thf('64', plain,
% 1.64/1.87      ((![X0 : $i]:
% 1.64/1.87          ((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (k1_tarski @ X0)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup+', [status(thm)], ['59', '63'])).
% 1.64/1.87  thf(t11_xboole_1, axiom,
% 1.64/1.87    (![A:$i,B:$i,C:$i]:
% 1.64/1.87     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.64/1.87  thf('65', plain,
% 1.64/1.87      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.64/1.87         ((r1_tarski @ X13 @ X14)
% 1.64/1.87          | ~ (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 1.64/1.87      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.64/1.87  thf('66', plain,
% 1.64/1.87      ((![X0 : $i, X1 : $i]:
% 1.64/1.87          (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r1_tarski @ sk_B_1 @ X1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['64', '65'])).
% 1.64/1.87  thf('67', plain,
% 1.64/1.87      (((((sk_C_1) = (sk_B_1)) | (r1_tarski @ sk_B_1 @ sk_C_1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['58', '66'])).
% 1.64/1.87  thf('68', plain,
% 1.64/1.87      (![X16 : $i, X17 : $i]:
% 1.64/1.87         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 1.64/1.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.64/1.87  thf('69', plain,
% 1.64/1.87      (((((sk_C_1) = (sk_B_1)) | ((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['67', '68'])).
% 1.64/1.87  thf('70', plain,
% 1.64/1.87      (((((k1_tarski @ sk_A) = (sk_C_1)) | ((sk_C_1) = (sk_B_1))))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup+', [status(thm)], ['22', '69'])).
% 1.64/1.87  thf('71', plain,
% 1.64/1.87      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('72', plain,
% 1.64/1.87      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.64/1.87         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('split', [status(esa)], ['71'])).
% 1.64/1.87  thf('73', plain,
% 1.64/1.87      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.64/1.87      inference('split', [status(esa)], ['71'])).
% 1.64/1.87  thf('74', plain,
% 1.64/1.87      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('75', plain,
% 1.64/1.87      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 1.64/1.87       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.64/1.87      inference('split', [status(esa)], ['74'])).
% 1.64/1.87  thf('76', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['33'])).
% 1.64/1.87  thf('77', plain,
% 1.64/1.87      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.64/1.87      inference('split', [status(esa)], ['71'])).
% 1.64/1.87  thf('78', plain,
% 1.64/1.87      ((((sk_B_1) != (sk_B_1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.64/1.87             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['76', '77'])).
% 1.64/1.87  thf('79', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.64/1.87      inference('simplify', [status(thm)], ['78'])).
% 1.64/1.87  thf('80', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.64/1.87      inference('sat_resolution*', [status(thm)], ['73', '75', '79'])).
% 1.64/1.87  thf('81', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.64/1.87      inference('simpl_trail', [status(thm)], ['72', '80'])).
% 1.64/1.87  thf('82', plain,
% 1.64/1.87      ((((sk_C_1) = (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify_reflect-', [status(thm)], ['70', '81'])).
% 1.64/1.87  thf('83', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.64/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.87  thf('84', plain,
% 1.64/1.87      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_B_1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup+', [status(thm)], ['82', '83'])).
% 1.64/1.87  thf('85', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.64/1.87      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.64/1.87  thf('86', plain,
% 1.64/1.87      ((((k1_tarski @ sk_A) = (sk_B_1)))
% 1.64/1.87         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.64/1.87  thf(t20_zfmisc_1, axiom,
% 1.64/1.87    (![A:$i,B:$i]:
% 1.64/1.87     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.64/1.87         ( k1_tarski @ A ) ) <=>
% 1.64/1.87       ( ( A ) != ( B ) ) ))).
% 1.64/1.87  thf('87', plain,
% 1.64/1.87      (![X42 : $i, X43 : $i]:
% 1.64/1.87         (((X43) != (X42))
% 1.64/1.87          | ((k4_xboole_0 @ (k1_tarski @ X43) @ (k1_tarski @ X42))
% 1.64/1.87              != (k1_tarski @ X43)))),
% 1.64/1.87      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 1.64/1.87  thf('88', plain,
% 1.64/1.87      (![X42 : $i]:
% 1.64/1.87         ((k4_xboole_0 @ (k1_tarski @ X42) @ (k1_tarski @ X42))
% 1.64/1.87           != (k1_tarski @ X42))),
% 1.64/1.87      inference('simplify', [status(thm)], ['87'])).
% 1.64/1.87  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.64/1.87      inference('sup+', [status(thm)], ['35', '36'])).
% 1.64/1.87  thf('90', plain, (![X42 : $i]: ((k1_xboole_0) != (k1_tarski @ X42))),
% 1.64/1.87      inference('demod', [status(thm)], ['88', '89'])).
% 1.64/1.87  thf('91', plain,
% 1.64/1.87      ((((k1_xboole_0) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('sup-', [status(thm)], ['86', '90'])).
% 1.64/1.87  thf('92', plain,
% 1.64/1.87      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('simplify', [status(thm)], ['33'])).
% 1.64/1.87  thf('93', plain,
% 1.64/1.87      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.64/1.87      inference('demod', [status(thm)], ['91', '92'])).
% 1.64/1.87  thf('94', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.64/1.87      inference('simplify', [status(thm)], ['93'])).
% 1.64/1.87  thf('95', plain,
% 1.64/1.87      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.64/1.87      inference('split', [status(esa)], ['20'])).
% 1.64/1.87  thf('96', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.64/1.87      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 1.64/1.87  thf('97', plain, (((sk_C_1) != (k1_xboole_0))),
% 1.64/1.87      inference('simpl_trail', [status(thm)], ['21', '96'])).
% 1.64/1.87  thf('98', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)),
% 1.64/1.87      inference('simplify_reflect-', [status(thm)], ['19', '97'])).
% 1.64/1.87  thf('99', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.64/1.87      inference('sup+', [status(thm)], ['27', '28'])).
% 1.64/1.87  thf('100', plain,
% 1.64/1.87      (![X16 : $i, X17 : $i]:
% 1.64/1.87         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 1.64/1.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.64/1.87  thf('101', plain,
% 1.64/1.87      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.64/1.87      inference('sup-', [status(thm)], ['99', '100'])).
% 1.64/1.87  thf('102', plain,
% 1.64/1.87      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.64/1.87         ((r1_tarski @ X13 @ X14)
% 1.64/1.87          | ~ (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 1.64/1.87      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.64/1.87  thf('103', plain,
% 1.64/1.87      (![X0 : $i]:
% 1.64/1.87         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 1.64/1.87      inference('sup-', [status(thm)], ['101', '102'])).
% 1.64/1.87  thf('104', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 1.64/1.87      inference('sup-', [status(thm)], ['98', '103'])).
% 1.64/1.87  thf('105', plain,
% 1.64/1.87      (![X16 : $i, X17 : $i]:
% 1.64/1.87         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 1.64/1.87      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.64/1.87  thf('106', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 1.64/1.87      inference('sup-', [status(thm)], ['104', '105'])).
% 1.64/1.87  thf('107', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 1.64/1.87      inference('sup+', [status(thm)], ['0', '106'])).
% 1.64/1.87  thf('108', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.64/1.87      inference('simpl_trail', [status(thm)], ['72', '80'])).
% 1.64/1.87  thf('109', plain, ($false),
% 1.64/1.87      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 1.64/1.87  
% 1.64/1.87  % SZS output end Refutation
% 1.64/1.87  
% 1.64/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
