%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.czsrZ8UqXs

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:32 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  255 (3658 expanded)
%              Number of leaves         :   30 (1092 expanded)
%              Depth                    :   30
%              Number of atoms          : 2018 (36647 expanded)
%              Number of equality atoms :  314 (5609 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r2_hidden @ X58 @ X59 )
      | ~ ( r1_tarski @ ( k1_tarski @ X58 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X58: $i,X60: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X58 ) @ X60 )
      | ~ ( r2_hidden @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X58: $i,X60: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X58 ) @ X60 )
      | ~ ( r2_hidden @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('23',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X17 @ X16 ) )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( ( k1_tarski @ sk_A )
        = sk_B_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_C_1
       != ( k1_tarski @ sk_A ) )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('42',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('45',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('46',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('47',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('48',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('52',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( ( k3_tarski @ sk_C_1 )
        = sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('55',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('57',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('58',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X58: $i,X60: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X58 ) @ X60 )
      | ~ ( r2_hidden @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('65',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
      | ( ( k1_tarski @ sk_A )
        = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('67',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('68',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
      | ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
        = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('70',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('71',plain,
    ( ( sk_B_1
     != ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) @ sk_C_1 )
      | ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
        = sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('76',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('78',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( r2_hidden @ ( k3_tarski @ sk_C_1 ) @ sk_C_1 )
      | ( ( k1_tarski @ sk_A )
        = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('81',plain,
    ( ( ( r2_hidden @ ( k3_tarski @ sk_C_1 ) @ sk_C_1 )
      | ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
        = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_B_1
     != ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('83',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_C_1 ) @ sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X58: $i,X60: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X58 ) @ X60 )
      | ~ ( r2_hidden @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('85',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) @ sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','85'])).

thf('87',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','86'])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X17 @ X16 ) )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('89',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('90',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,
    ( ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['89','95'])).

thf('97',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','85'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('98',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('99',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( X0
          = ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( ( sk_B @ sk_B_1 )
        = ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('103',plain,(
    ! [X58: $i,X60: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X58 ) @ X60 )
      | ~ ( r2_hidden @ X58 @ X60 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','85'])).

thf('107',plain,
    ( ( ( r1_tarski @ sk_C_1 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_C_1 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('110',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) @ sk_B_1 )
      | ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
        = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_B_1
     != ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('113',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','85'])).

thf('115',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','115'])).

thf('117',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('118',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('121',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('122',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X17 @ X16 ) )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('123',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('124',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('125',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('126',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('127',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['123','127'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('129',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('130',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('131',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['128','129','130'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('132',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('133',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('135',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['133','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('145',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['143','146'])).

thf('148',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['120','147'])).

thf('149',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('150',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['150','154'])).

thf('156',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['149','155'])).

thf('157',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('158',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('160',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X17 @ X16 ) )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('166',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['163','164','167'])).

thf('169',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_tarski @ ( sk_B @ X0 ) ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['158','173'])).

thf('175',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['148','175'])).

thf('177',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('180',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('182',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('183',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_1 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['180','183'])).

thf('185',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('186',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('187',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('189',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ X22 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('192',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k5_xboole_0 @ X24 @ ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['193','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['190','200'])).

thf('202',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['193','199'])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['193','199'])).

thf('207',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','187','205','206'])).

thf('208',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( ( k5_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      = sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['207','210'])).

thf('212',plain,
    ( ( ( ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 )
        = sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['177','211'])).

thf('213',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('214',plain,
    ( ( ( sk_C_1 = sk_B_1 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('216',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('217',plain,
    ( ( sk_C_1 != sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['214','217'])).

thf('219',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('220',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1
       != ( k1_tarski @ sk_A ) )
      & ( sk_C_1 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('223',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['40','41','43','119','221','222'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.czsrZ8UqXs
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.74/1.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.74/1.96  % Solved by: fo/fo7.sh
% 1.74/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.74/1.96  % done 3409 iterations in 1.507s
% 1.74/1.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.74/1.96  % SZS output start Refutation
% 1.74/1.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.74/1.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.74/1.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.74/1.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.74/1.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.74/1.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.74/1.96  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.74/1.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(sk_B_type, type, sk_B: $i > $i).
% 1.74/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.74/1.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.74/1.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.74/1.96  thf(d10_xboole_0, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.74/1.96  thf('0', plain,
% 1.74/1.96      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.74/1.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.96  thf('1', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.74/1.96      inference('simplify', [status(thm)], ['0'])).
% 1.74/1.96  thf(l1_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.74/1.96  thf('2', plain,
% 1.74/1.96      (![X58 : $i, X59 : $i]:
% 1.74/1.96         ((r2_hidden @ X58 @ X59) | ~ (r1_tarski @ (k1_tarski @ X58) @ X59))),
% 1.74/1.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.74/1.96  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.96  thf(t43_zfmisc_1, conjecture,
% 1.74/1.96    (![A:$i,B:$i,C:$i]:
% 1.74/1.96     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.74/1.96          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.74/1.96          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.74/1.96          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.74/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.74/1.96    (~( ![A:$i,B:$i,C:$i]:
% 1.74/1.96        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.74/1.96             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.74/1.96             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.74/1.96             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.74/1.96    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.74/1.96  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(l51_zfmisc_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.74/1.96  thf('5', plain,
% 1.74/1.96      (![X61 : $i, X62 : $i]:
% 1.74/1.96         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.74/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.96  thf('6', plain,
% 1.74/1.96      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 1.74/1.96      inference('demod', [status(thm)], ['4', '5'])).
% 1.74/1.96  thf(d3_xboole_0, axiom,
% 1.74/1.96    (![A:$i,B:$i,C:$i]:
% 1.74/1.96     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.74/1.96       ( ![D:$i]:
% 1.74/1.96         ( ( r2_hidden @ D @ C ) <=>
% 1.74/1.96           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.74/1.96  thf('7', plain,
% 1.74/1.96      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.74/1.96         (~ (r2_hidden @ X4 @ X2)
% 1.74/1.96          | (r2_hidden @ X4 @ X3)
% 1.74/1.96          | (r2_hidden @ X4 @ X1)
% 1.74/1.96          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.74/1.96      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.74/1.96  thf('8', plain,
% 1.74/1.96      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.74/1.96         ((r2_hidden @ X4 @ X1)
% 1.74/1.96          | (r2_hidden @ X4 @ X3)
% 1.74/1.96          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['7'])).
% 1.74/1.96  thf('9', plain,
% 1.74/1.96      (![X61 : $i, X62 : $i]:
% 1.74/1.96         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.74/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.96  thf('10', plain,
% 1.74/1.96      (![X1 : $i, X3 : $i, X4 : $i]:
% 1.74/1.96         ((r2_hidden @ X4 @ X1)
% 1.74/1.96          | (r2_hidden @ X4 @ X3)
% 1.74/1.96          | ~ (r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X3 @ X1))))),
% 1.74/1.96      inference('demod', [status(thm)], ['8', '9'])).
% 1.74/1.96  thf('11', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.74/1.96          | (r2_hidden @ X0 @ sk_B_1)
% 1.74/1.96          | (r2_hidden @ X0 @ sk_C_1))),
% 1.74/1.96      inference('sup-', [status(thm)], ['6', '10'])).
% 1.74/1.96  thf('12', plain,
% 1.74/1.96      (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 1.74/1.96      inference('sup-', [status(thm)], ['3', '11'])).
% 1.74/1.96  thf('13', plain,
% 1.74/1.96      (![X58 : $i, X60 : $i]:
% 1.74/1.96         ((r1_tarski @ (k1_tarski @ X58) @ X60) | ~ (r2_hidden @ X58 @ X60))),
% 1.74/1.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.74/1.96  thf('14', plain,
% 1.74/1.96      (((r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1))),
% 1.74/1.96      inference('sup-', [status(thm)], ['12', '13'])).
% 1.74/1.96  thf('15', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf(t11_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i,C:$i]:
% 1.74/1.96     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.74/1.96  thf('16', plain,
% 1.74/1.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.74/1.96         ((r1_tarski @ X13 @ X14)
% 1.74/1.96          | ~ (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 1.74/1.96      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.74/1.96  thf('17', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['15', '16'])).
% 1.74/1.96  thf('18', plain,
% 1.74/1.96      (((r2_hidden @ sk_A @ sk_B_1) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 1.74/1.96      inference('sup-', [status(thm)], ['14', '17'])).
% 1.74/1.96  thf('19', plain,
% 1.74/1.96      (![X58 : $i, X60 : $i]:
% 1.74/1.96         ((r1_tarski @ (k1_tarski @ X58) @ X60) | ~ (r2_hidden @ X58 @ X60))),
% 1.74/1.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.74/1.96  thf('20', plain,
% 1.74/1.96      (((r1_tarski @ sk_B_1 @ sk_C_1)
% 1.74/1.96        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.74/1.96      inference('sup-', [status(thm)], ['18', '19'])).
% 1.74/1.96  thf('21', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.74/1.96      inference('simplify', [status(thm)], ['0'])).
% 1.74/1.96  thf('22', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['15', '16'])).
% 1.74/1.96  thf('23', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.74/1.96      inference('sup-', [status(thm)], ['21', '22'])).
% 1.74/1.96  thf('24', plain,
% 1.74/1.96      (![X8 : $i, X10 : $i]:
% 1.74/1.96         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.74/1.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.96  thf('25', plain,
% 1.74/1.96      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.74/1.96        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['23', '24'])).
% 1.74/1.96  thf('26', plain,
% 1.74/1.96      (((r1_tarski @ sk_B_1 @ sk_C_1) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['20', '25'])).
% 1.74/1.96  thf(t12_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.74/1.96  thf('27', plain,
% 1.74/1.96      (![X16 : $i, X17 : $i]:
% 1.74/1.96         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 1.74/1.96      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.74/1.96  thf('28', plain,
% 1.74/1.96      (![X61 : $i, X62 : $i]:
% 1.74/1.96         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.74/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.96  thf('29', plain,
% 1.74/1.96      (![X16 : $i, X17 : $i]:
% 1.74/1.96         (((k3_tarski @ (k2_tarski @ X17 @ X16)) = (X16))
% 1.74/1.96          | ~ (r1_tarski @ X17 @ X16))),
% 1.74/1.96      inference('demod', [status(thm)], ['27', '28'])).
% 1.74/1.96  thf('30', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_B_1))
% 1.74/1.96        | ((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (sk_C_1)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['26', '29'])).
% 1.74/1.96  thf('31', plain,
% 1.74/1.96      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 1.74/1.96      inference('demod', [status(thm)], ['4', '5'])).
% 1.74/1.96  thf('32', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['30', '31'])).
% 1.74/1.96  thf('33', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('34', plain,
% 1.74/1.96      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('split', [status(esa)], ['33'])).
% 1.74/1.96  thf('35', plain,
% 1.74/1.96      (((((sk_C_1) != (sk_C_1)) | ((k1_tarski @ sk_A) = (sk_B_1))))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['32', '34'])).
% 1.74/1.96  thf('36', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_B_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['35'])).
% 1.74/1.96  thf('37', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('38', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('split', [status(esa)], ['37'])).
% 1.74/1.96  thf('39', plain,
% 1.74/1.96      ((((sk_B_1) != (sk_B_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))) & 
% 1.74/1.96             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['36', '38'])).
% 1.74/1.96  thf('40', plain,
% 1.74/1.96      ((((sk_B_1) = (k1_tarski @ sk_A))) | (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['39'])).
% 1.74/1.96  thf('41', plain,
% 1.74/1.96      (~ (((sk_B_1) = (k1_xboole_0))) | ~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('split', [status(esa)], ['33'])).
% 1.74/1.96  thf('42', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.74/1.96  thf('43', plain,
% 1.74/1.96      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 1.74/1.96       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('split', [status(esa)], ['42'])).
% 1.74/1.96  thf('44', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['30', '31'])).
% 1.74/1.96  thf(t69_enumset1, axiom,
% 1.74/1.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.74/1.96  thf('45', plain,
% 1.74/1.96      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 1.74/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.96  thf(idempotence_k2_xboole_0, axiom,
% 1.74/1.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.74/1.96  thf('46', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.74/1.96      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.74/1.96  thf('47', plain,
% 1.74/1.96      (![X61 : $i, X62 : $i]:
% 1.74/1.96         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.74/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.96  thf('48', plain, (![X6 : $i]: ((k3_tarski @ (k2_tarski @ X6 @ X6)) = (X6))),
% 1.74/1.96      inference('demod', [status(thm)], ['46', '47'])).
% 1.74/1.96  thf('49', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['45', '48'])).
% 1.74/1.96  thf('50', plain,
% 1.74/1.96      ((((k3_tarski @ sk_C_1) = (sk_A)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['44', '49'])).
% 1.74/1.96  thf('51', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('split', [status(esa)], ['37'])).
% 1.74/1.96  thf('52', plain,
% 1.74/1.96      (((((sk_B_1) != (sk_B_1)) | ((k3_tarski @ sk_C_1) = (sk_A))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['50', '51'])).
% 1.74/1.96  thf('53', plain,
% 1.74/1.96      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['52'])).
% 1.74/1.96  thf('54', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.74/1.96      inference('sup-', [status(thm)], ['21', '22'])).
% 1.74/1.96  thf('55', plain,
% 1.74/1.96      (((r1_tarski @ sk_B_1 @ (k1_tarski @ (k3_tarski @ sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.96  thf('56', plain,
% 1.74/1.96      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['52'])).
% 1.74/1.96  thf('57', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['30', '31'])).
% 1.74/1.96  thf('58', plain,
% 1.74/1.96      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 1.74/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.96  thf('59', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.96  thf('60', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['58', '59'])).
% 1.74/1.96  thf('61', plain,
% 1.74/1.96      (![X58 : $i, X60 : $i]:
% 1.74/1.96         ((r1_tarski @ (k1_tarski @ X58) @ X60) | ~ (r2_hidden @ X58 @ X60))),
% 1.74/1.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.74/1.96  thf('62', plain,
% 1.74/1.96      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['60', '61'])).
% 1.74/1.96  thf('63', plain,
% 1.74/1.96      (((r1_tarski @ sk_C_1 @ (k2_tarski @ sk_A @ sk_A))
% 1.74/1.96        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['57', '62'])).
% 1.74/1.96  thf('64', plain,
% 1.74/1.96      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 1.74/1.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.74/1.96  thf('65', plain,
% 1.74/1.96      (((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))
% 1.74/1.96        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('demod', [status(thm)], ['63', '64'])).
% 1.74/1.96  thf('66', plain,
% 1.74/1.96      ((((r1_tarski @ sk_C_1 @ (k1_tarski @ (k3_tarski @ sk_C_1)))
% 1.74/1.96         | ((k1_tarski @ sk_A) = (sk_B_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['56', '65'])).
% 1.74/1.96  thf('67', plain,
% 1.74/1.96      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['52'])).
% 1.74/1.96  thf('68', plain,
% 1.74/1.96      ((((r1_tarski @ sk_C_1 @ (k1_tarski @ (k3_tarski @ sk_C_1)))
% 1.74/1.96         | ((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_B_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['66', '67'])).
% 1.74/1.96  thf('69', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('split', [status(esa)], ['37'])).
% 1.74/1.96  thf('70', plain,
% 1.74/1.96      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['52'])).
% 1.74/1.96  thf('71', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_tarski @ (k3_tarski @ sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['69', '70'])).
% 1.74/1.96  thf('72', plain,
% 1.74/1.96      (((r1_tarski @ sk_C_1 @ (k1_tarski @ (k3_tarski @ sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify_reflect-', [status(thm)], ['68', '71'])).
% 1.74/1.96  thf('73', plain,
% 1.74/1.96      (![X8 : $i, X10 : $i]:
% 1.74/1.96         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.74/1.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.96  thf('74', plain,
% 1.74/1.96      (((~ (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_C_1)) @ sk_C_1)
% 1.74/1.96         | ((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['72', '73'])).
% 1.74/1.96  thf('75', plain,
% 1.74/1.96      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['52'])).
% 1.74/1.96  thf('76', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['30', '31'])).
% 1.74/1.96  thf('77', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['1', '2'])).
% 1.74/1.96  thf('78', plain,
% 1.74/1.96      (((r2_hidden @ sk_A @ sk_C_1) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['76', '77'])).
% 1.74/1.96  thf('79', plain,
% 1.74/1.96      ((((r2_hidden @ (k3_tarski @ sk_C_1) @ sk_C_1)
% 1.74/1.96         | ((k1_tarski @ sk_A) = (sk_B_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['75', '78'])).
% 1.74/1.96  thf('80', plain,
% 1.74/1.96      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['52'])).
% 1.74/1.96  thf('81', plain,
% 1.74/1.96      ((((r2_hidden @ (k3_tarski @ sk_C_1) @ sk_C_1)
% 1.74/1.96         | ((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_B_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['79', '80'])).
% 1.74/1.96  thf('82', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_tarski @ (k3_tarski @ sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['69', '70'])).
% 1.74/1.96  thf('83', plain,
% 1.74/1.96      (((r2_hidden @ (k3_tarski @ sk_C_1) @ sk_C_1))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 1.74/1.96  thf('84', plain,
% 1.74/1.96      (![X58 : $i, X60 : $i]:
% 1.74/1.96         ((r1_tarski @ (k1_tarski @ X58) @ X60) | ~ (r2_hidden @ X58 @ X60))),
% 1.74/1.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.74/1.96  thf('85', plain,
% 1.74/1.96      (((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_C_1)) @ sk_C_1))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['83', '84'])).
% 1.74/1.96  thf('86', plain,
% 1.74/1.96      ((((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_C_1)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['74', '85'])).
% 1.74/1.96  thf('87', plain,
% 1.74/1.96      (((r1_tarski @ sk_B_1 @ sk_C_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['55', '86'])).
% 1.74/1.96  thf('88', plain,
% 1.74/1.96      (![X16 : $i, X17 : $i]:
% 1.74/1.96         (((k3_tarski @ (k2_tarski @ X17 @ X16)) = (X16))
% 1.74/1.96          | ~ (r1_tarski @ X17 @ X16))),
% 1.74/1.96      inference('demod', [status(thm)], ['27', '28'])).
% 1.74/1.96  thf('89', plain,
% 1.74/1.96      ((((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)) = (sk_C_1)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['87', '88'])).
% 1.74/1.96  thf(t7_xboole_0, axiom,
% 1.74/1.96    (![A:$i]:
% 1.74/1.96     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.74/1.96          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.74/1.96  thf('90', plain,
% 1.74/1.96      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.74/1.96      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.74/1.96  thf('91', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.74/1.96         (~ (r2_hidden @ X0 @ X3)
% 1.74/1.96          | (r2_hidden @ X0 @ X2)
% 1.74/1.96          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.74/1.96      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.74/1.96  thf('92', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.74/1.96         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 1.74/1.96      inference('simplify', [status(thm)], ['91'])).
% 1.74/1.96  thf('93', plain,
% 1.74/1.96      (![X61 : $i, X62 : $i]:
% 1.74/1.96         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.74/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.96  thf('94', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.74/1.96         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 1.74/1.96          | ~ (r2_hidden @ X0 @ X3))),
% 1.74/1.96      inference('demod', [status(thm)], ['92', '93'])).
% 1.74/1.96  thf('95', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         (((X0) = (k1_xboole_0))
% 1.74/1.96          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ (k2_tarski @ X0 @ X1))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['90', '94'])).
% 1.74/1.96  thf('96', plain,
% 1.74/1.96      ((((r2_hidden @ (sk_B @ sk_B_1) @ sk_C_1) | ((sk_B_1) = (k1_xboole_0))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['89', '95'])).
% 1.74/1.96  thf('97', plain,
% 1.74/1.96      ((((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_C_1)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['74', '85'])).
% 1.74/1.96  thf(d1_tarski, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.74/1.96       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.74/1.96  thf('98', plain,
% 1.74/1.96      (![X25 : $i, X27 : $i, X28 : $i]:
% 1.74/1.96         (~ (r2_hidden @ X28 @ X27)
% 1.74/1.96          | ((X28) = (X25))
% 1.74/1.96          | ((X27) != (k1_tarski @ X25)))),
% 1.74/1.96      inference('cnf', [status(esa)], [d1_tarski])).
% 1.74/1.96  thf('99', plain,
% 1.74/1.96      (![X25 : $i, X28 : $i]:
% 1.74/1.96         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['98'])).
% 1.74/1.96  thf('100', plain,
% 1.74/1.96      ((![X0 : $i]:
% 1.74/1.96          (~ (r2_hidden @ X0 @ sk_C_1) | ((X0) = (k3_tarski @ sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['97', '99'])).
% 1.74/1.96  thf('101', plain,
% 1.74/1.96      (((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (k3_tarski @ sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['96', '100'])).
% 1.74/1.96  thf('102', plain,
% 1.74/1.96      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.74/1.96      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.74/1.96  thf('103', plain,
% 1.74/1.96      (![X58 : $i, X60 : $i]:
% 1.74/1.96         ((r1_tarski @ (k1_tarski @ X58) @ X60) | ~ (r2_hidden @ X58 @ X60))),
% 1.74/1.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.74/1.96  thf('104', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['102', '103'])).
% 1.74/1.96  thf('105', plain,
% 1.74/1.96      ((((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_C_1)) @ sk_B_1)
% 1.74/1.96         | ((sk_B_1) = (k1_xboole_0))
% 1.74/1.96         | ((sk_B_1) = (k1_xboole_0))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['101', '104'])).
% 1.74/1.96  thf('106', plain,
% 1.74/1.96      ((((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_C_1)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['74', '85'])).
% 1.74/1.96  thf('107', plain,
% 1.74/1.96      ((((r1_tarski @ sk_C_1 @ sk_B_1)
% 1.74/1.96         | ((sk_B_1) = (k1_xboole_0))
% 1.74/1.96         | ((sk_B_1) = (k1_xboole_0))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['105', '106'])).
% 1.74/1.96  thf('108', plain,
% 1.74/1.96      (((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ sk_C_1 @ sk_B_1)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['107'])).
% 1.74/1.96  thf('109', plain,
% 1.74/1.96      (((r1_tarski @ sk_B_1 @ (k1_tarski @ (k3_tarski @ sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['53', '54'])).
% 1.74/1.96  thf('110', plain,
% 1.74/1.96      (![X8 : $i, X10 : $i]:
% 1.74/1.96         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.74/1.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.74/1.96  thf('111', plain,
% 1.74/1.96      (((~ (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_C_1)) @ sk_B_1)
% 1.74/1.96         | ((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_B_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['109', '110'])).
% 1.74/1.96  thf('112', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_tarski @ (k3_tarski @ sk_C_1))))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['69', '70'])).
% 1.74/1.96  thf('113', plain,
% 1.74/1.96      ((~ (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_C_1)) @ sk_B_1))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 1.74/1.96  thf('114', plain,
% 1.74/1.96      ((((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_C_1)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['74', '85'])).
% 1.74/1.96  thf('115', plain,
% 1.74/1.96      ((~ (r1_tarski @ sk_C_1 @ sk_B_1))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['113', '114'])).
% 1.74/1.96  thf('116', plain,
% 1.74/1.96      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('clc', [status(thm)], ['108', '115'])).
% 1.74/1.96  thf('117', plain,
% 1.74/1.96      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.74/1.96      inference('split', [status(esa)], ['33'])).
% 1.74/1.96  thf('118', plain,
% 1.74/1.96      ((((sk_B_1) != (sk_B_1)))
% 1.74/1.96         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.74/1.96             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['116', '117'])).
% 1.74/1.96  thf('119', plain,
% 1.74/1.96      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['118'])).
% 1.74/1.96  thf('120', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_C_1)) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['30', '31'])).
% 1.74/1.96  thf('121', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.74/1.96      inference('sup-', [status(thm)], ['21', '22'])).
% 1.74/1.96  thf('122', plain,
% 1.74/1.96      (![X16 : $i, X17 : $i]:
% 1.74/1.96         (((k3_tarski @ (k2_tarski @ X17 @ X16)) = (X16))
% 1.74/1.96          | ~ (r1_tarski @ X17 @ X16))),
% 1.74/1.96      inference('demod', [status(thm)], ['27', '28'])).
% 1.74/1.96  thf('123', plain,
% 1.74/1.96      (((k3_tarski @ (k2_tarski @ sk_B_1 @ (k1_tarski @ sk_A)))
% 1.74/1.96         = (k1_tarski @ sk_A))),
% 1.74/1.96      inference('sup-', [status(thm)], ['121', '122'])).
% 1.74/1.96  thf(t95_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k3_xboole_0 @ A @ B ) =
% 1.74/1.96       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.74/1.96  thf('124', plain,
% 1.74/1.96      (![X23 : $i, X24 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ X23 @ X24)
% 1.74/1.96           = (k5_xboole_0 @ (k5_xboole_0 @ X23 @ X24) @ 
% 1.74/1.96              (k2_xboole_0 @ X23 @ X24)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.74/1.96  thf('125', plain,
% 1.74/1.96      (![X61 : $i, X62 : $i]:
% 1.74/1.96         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.74/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.96  thf(t91_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i,C:$i]:
% 1.74/1.96     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.74/1.96       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.74/1.96  thf('126', plain,
% 1.74/1.96      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.74/1.96           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.74/1.96  thf('127', plain,
% 1.74/1.96      (![X23 : $i, X24 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ X23 @ X24)
% 1.74/1.96           = (k5_xboole_0 @ X23 @ 
% 1.74/1.96              (k5_xboole_0 @ X24 @ (k3_tarski @ (k2_tarski @ X23 @ X24)))))),
% 1.74/1.96      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.96  thf('128', plain,
% 1.74/1.96      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 1.74/1.96         = (k5_xboole_0 @ sk_B_1 @ 
% 1.74/1.96            (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['123', '127'])).
% 1.74/1.96  thf(t92_xboole_1, axiom,
% 1.74/1.96    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.74/1.96  thf('129', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.74/1.96  thf(t5_boole, axiom,
% 1.74/1.96    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.74/1.96  thf('130', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.74/1.96      inference('cnf', [status(esa)], [t5_boole])).
% 1.74/1.96  thf('131', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 1.74/1.96      inference('demod', [status(thm)], ['128', '129', '130'])).
% 1.74/1.96  thf(t100_xboole_1, axiom,
% 1.74/1.96    (![A:$i,B:$i]:
% 1.74/1.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.74/1.96  thf('132', plain,
% 1.74/1.96      (![X11 : $i, X12 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X11 @ X12)
% 1.74/1.96           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.96  thf('133', plain,
% 1.74/1.96      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 1.74/1.96         = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 1.74/1.96      inference('sup+', [status(thm)], ['131', '132'])).
% 1.74/1.96  thf('134', plain, (![X6 : $i]: ((k3_tarski @ (k2_tarski @ X6 @ X6)) = (X6))),
% 1.74/1.96      inference('demod', [status(thm)], ['46', '47'])).
% 1.74/1.96  thf('135', plain,
% 1.74/1.96      (![X23 : $i, X24 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ X23 @ X24)
% 1.74/1.96           = (k5_xboole_0 @ X23 @ 
% 1.74/1.96              (k5_xboole_0 @ X24 @ (k3_tarski @ (k2_tarski @ X23 @ X24)))))),
% 1.74/1.96      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.96  thf('136', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ X0 @ X0)
% 1.74/1.96           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['134', '135'])).
% 1.74/1.96  thf('137', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.74/1.96  thf('138', plain,
% 1.74/1.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.74/1.96      inference('demod', [status(thm)], ['136', '137'])).
% 1.74/1.96  thf('139', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.74/1.96      inference('cnf', [status(esa)], [t5_boole])).
% 1.74/1.96  thf('140', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.74/1.96      inference('demod', [status(thm)], ['138', '139'])).
% 1.74/1.96  thf('141', plain,
% 1.74/1.96      (![X11 : $i, X12 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X11 @ X12)
% 1.74/1.96           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.96  thf('142', plain,
% 1.74/1.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['140', '141'])).
% 1.74/1.96  thf('143', plain,
% 1.74/1.96      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 1.74/1.96         = (k4_xboole_0 @ sk_B_1 @ sk_B_1))),
% 1.74/1.96      inference('demod', [status(thm)], ['133', '142'])).
% 1.74/1.96  thf('144', plain,
% 1.74/1.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['140', '141'])).
% 1.74/1.96  thf('145', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.74/1.96  thf('146', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['144', '145'])).
% 1.74/1.96  thf('147', plain,
% 1.74/1.96      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 1.74/1.96      inference('demod', [status(thm)], ['143', '146'])).
% 1.74/1.96  thf('148', plain,
% 1.74/1.96      ((((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 1.74/1.96        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['120', '147'])).
% 1.74/1.96  thf('149', plain,
% 1.74/1.96      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 1.74/1.96      inference('demod', [status(thm)], ['4', '5'])).
% 1.74/1.96  thf('150', plain,
% 1.74/1.96      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 1.74/1.96      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.74/1.96  thf('151', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.74/1.96         (~ (r2_hidden @ X0 @ X1)
% 1.74/1.96          | (r2_hidden @ X0 @ X2)
% 1.74/1.96          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 1.74/1.96      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.74/1.96  thf('152', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.74/1.96         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 1.74/1.96      inference('simplify', [status(thm)], ['151'])).
% 1.74/1.96  thf('153', plain,
% 1.74/1.96      (![X61 : $i, X62 : $i]:
% 1.74/1.96         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.74/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.74/1.96  thf('154', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.74/1.96         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 1.74/1.96          | ~ (r2_hidden @ X0 @ X1))),
% 1.74/1.96      inference('demod', [status(thm)], ['152', '153'])).
% 1.74/1.96  thf('155', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         (((X0) = (k1_xboole_0))
% 1.74/1.96          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['150', '154'])).
% 1.74/1.96  thf('156', plain,
% 1.74/1.96      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 1.74/1.96        | ((sk_C_1) = (k1_xboole_0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['149', '155'])).
% 1.74/1.96  thf('157', plain,
% 1.74/1.96      (![X25 : $i, X28 : $i]:
% 1.74/1.96         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['98'])).
% 1.74/1.96  thf('158', plain,
% 1.74/1.96      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['156', '157'])).
% 1.74/1.96  thf('159', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 1.74/1.96      inference('sup-', [status(thm)], ['102', '103'])).
% 1.74/1.96  thf('160', plain,
% 1.74/1.96      (![X16 : $i, X17 : $i]:
% 1.74/1.96         (((k3_tarski @ (k2_tarski @ X17 @ X16)) = (X16))
% 1.74/1.96          | ~ (r1_tarski @ X17 @ X16))),
% 1.74/1.96      inference('demod', [status(thm)], ['27', '28'])).
% 1.74/1.96  thf('161', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((X0) = (k1_xboole_0))
% 1.74/1.96          | ((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)) = (X0)))),
% 1.74/1.96      inference('sup-', [status(thm)], ['159', '160'])).
% 1.74/1.96  thf('162', plain,
% 1.74/1.96      (![X23 : $i, X24 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ X23 @ X24)
% 1.74/1.96           = (k5_xboole_0 @ X23 @ 
% 1.74/1.96              (k5_xboole_0 @ X24 @ (k3_tarski @ (k2_tarski @ X23 @ X24)))))),
% 1.74/1.96      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.96  thf('163', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((k3_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 1.74/1.96            = (k5_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ 
% 1.74/1.96               (k5_xboole_0 @ X0 @ X0)))
% 1.74/1.96          | ((X0) = (k1_xboole_0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['161', '162'])).
% 1.74/1.96  thf('164', plain,
% 1.74/1.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['140', '141'])).
% 1.74/1.96  thf('165', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['144', '145'])).
% 1.74/1.96  thf('166', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.74/1.96      inference('cnf', [status(esa)], [t5_boole])).
% 1.74/1.96  thf('167', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 1.74/1.96      inference('sup+', [status(thm)], ['165', '166'])).
% 1.74/1.96  thf('168', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((k3_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 1.74/1.96            = (k1_tarski @ (sk_B @ X0)))
% 1.74/1.96          | ((X0) = (k1_xboole_0)))),
% 1.74/1.96      inference('demod', [status(thm)], ['163', '164', '167'])).
% 1.74/1.96  thf('169', plain,
% 1.74/1.96      (![X11 : $i, X12 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X11 @ X12)
% 1.74/1.96           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.96  thf('170', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((k4_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 1.74/1.96            = (k5_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ 
% 1.74/1.96               (k1_tarski @ (sk_B @ X0))))
% 1.74/1.96          | ((X0) = (k1_xboole_0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['168', '169'])).
% 1.74/1.96  thf('171', plain,
% 1.74/1.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['140', '141'])).
% 1.74/1.96  thf('172', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['144', '145'])).
% 1.74/1.96  thf('173', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         (((k4_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (k1_xboole_0))
% 1.74/1.96          | ((X0) = (k1_xboole_0)))),
% 1.74/1.96      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.74/1.96  thf('174', plain,
% 1.74/1.96      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (k1_xboole_0))
% 1.74/1.96        | ((sk_C_1) = (k1_xboole_0))
% 1.74/1.96        | ((sk_C_1) = (k1_xboole_0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['158', '173'])).
% 1.74/1.96  thf('175', plain,
% 1.74/1.96      ((((sk_C_1) = (k1_xboole_0))
% 1.74/1.96        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (k1_xboole_0)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['174'])).
% 1.74/1.96  thf('176', plain,
% 1.74/1.96      ((((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 1.74/1.96        | ((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 1.74/1.96        | ((sk_C_1) = (k1_xboole_0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['148', '175'])).
% 1.74/1.96  thf('177', plain,
% 1.74/1.96      ((((sk_C_1) = (k1_xboole_0))
% 1.74/1.96        | ((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_xboole_0)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['176'])).
% 1.74/1.96  thf('178', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_B_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['35'])).
% 1.74/1.96  thf('179', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['45', '48'])).
% 1.74/1.96  thf('180', plain,
% 1.74/1.96      ((((k3_tarski @ sk_B_1) = (sk_A)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['178', '179'])).
% 1.74/1.96  thf('181', plain,
% 1.74/1.96      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C_1)))),
% 1.74/1.96      inference('demod', [status(thm)], ['4', '5'])).
% 1.74/1.96  thf('182', plain,
% 1.74/1.96      (![X23 : $i, X24 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ X23 @ X24)
% 1.74/1.96           = (k5_xboole_0 @ X23 @ 
% 1.74/1.96              (k5_xboole_0 @ X24 @ (k3_tarski @ (k2_tarski @ X23 @ X24)))))),
% 1.74/1.96      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.96  thf('183', plain,
% 1.74/1.96      (((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 1.74/1.96         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['181', '182'])).
% 1.74/1.96  thf('184', plain,
% 1.74/1.96      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1)
% 1.74/1.96          = (k5_xboole_0 @ sk_B_1 @ 
% 1.74/1.96             (k5_xboole_0 @ sk_C_1 @ (k1_tarski @ (k3_tarski @ sk_B_1))))))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['180', '183'])).
% 1.74/1.96  thf('185', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_B_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['35'])).
% 1.74/1.96  thf('186', plain,
% 1.74/1.96      ((((k3_tarski @ sk_B_1) = (sk_A)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['178', '179'])).
% 1.74/1.96  thf('187', plain,
% 1.74/1.96      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['185', '186'])).
% 1.74/1.96  thf('188', plain,
% 1.74/1.96      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.74/1.96           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.74/1.96  thf('189', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.74/1.96  thf('190', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 1.74/1.96           = (k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['188', '189'])).
% 1.74/1.96  thf('191', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ X22) = (k1_xboole_0))),
% 1.74/1.96      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.74/1.96  thf('192', plain,
% 1.74/1.96      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 1.74/1.96           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.74/1.96  thf('193', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.74/1.96           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['191', '192'])).
% 1.74/1.96  thf('194', plain,
% 1.74/1.96      (![X23 : $i, X24 : $i]:
% 1.74/1.96         ((k3_xboole_0 @ X23 @ X24)
% 1.74/1.96           = (k5_xboole_0 @ X23 @ 
% 1.74/1.96              (k5_xboole_0 @ X24 @ (k3_tarski @ (k2_tarski @ X23 @ X24)))))),
% 1.74/1.96      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.74/1.96  thf('195', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.74/1.96           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.96      inference('sup+', [status(thm)], ['191', '192'])).
% 1.74/1.96  thf('196', plain,
% 1.74/1.96      (![X0 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ k1_xboole_0 @ (k3_tarski @ (k2_tarski @ X0 @ X0)))
% 1.74/1.96           = (k3_xboole_0 @ X0 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['194', '195'])).
% 1.74/1.96  thf('197', plain, (![X6 : $i]: ((k3_tarski @ (k2_tarski @ X6 @ X6)) = (X6))),
% 1.74/1.96      inference('demod', [status(thm)], ['46', '47'])).
% 1.74/1.96  thf('198', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.74/1.96      inference('demod', [status(thm)], ['138', '139'])).
% 1.74/1.96  thf('199', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.74/1.96      inference('demod', [status(thm)], ['196', '197', '198'])).
% 1.74/1.96  thf('200', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.96      inference('demod', [status(thm)], ['193', '199'])).
% 1.74/1.96  thf('201', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 1.74/1.96           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['190', '200'])).
% 1.74/1.96  thf('202', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.74/1.96      inference('cnf', [status(esa)], [t5_boole])).
% 1.74/1.96  thf('203', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.74/1.96      inference('demod', [status(thm)], ['201', '202'])).
% 1.74/1.96  thf('204', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.96      inference('demod', [status(thm)], ['193', '199'])).
% 1.74/1.96  thf('205', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 1.74/1.96      inference('sup+', [status(thm)], ['203', '204'])).
% 1.74/1.96  thf('206', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.74/1.96      inference('demod', [status(thm)], ['193', '199'])).
% 1.74/1.96  thf('207', plain,
% 1.74/1.96      ((((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['184', '187', '205', '206'])).
% 1.74/1.96  thf('208', plain,
% 1.74/1.96      (![X11 : $i, X12 : $i]:
% 1.74/1.96         ((k4_xboole_0 @ X11 @ X12)
% 1.74/1.96           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.74/1.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.74/1.96  thf('209', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 1.74/1.96      inference('demod', [status(thm)], ['201', '202'])).
% 1.74/1.96  thf('210', plain,
% 1.74/1.96      (![X0 : $i, X1 : $i]:
% 1.74/1.96         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.74/1.96           = (X1))),
% 1.74/1.96      inference('sup+', [status(thm)], ['208', '209'])).
% 1.74/1.96  thf('211', plain,
% 1.74/1.96      ((((k5_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_B_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['207', '210'])).
% 1.74/1.96  thf('212', plain,
% 1.74/1.96      (((((k5_xboole_0 @ sk_C_1 @ k1_xboole_0) = (sk_B_1))
% 1.74/1.96         | ((sk_C_1) = (k1_xboole_0))))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('sup+', [status(thm)], ['177', '211'])).
% 1.74/1.96  thf('213', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.74/1.96      inference('cnf', [status(esa)], [t5_boole])).
% 1.74/1.96  thf('214', plain,
% 1.74/1.96      (((((sk_C_1) = (sk_B_1)) | ((sk_C_1) = (k1_xboole_0))))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['212', '213'])).
% 1.74/1.96  thf('215', plain,
% 1.74/1.96      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('split', [status(esa)], ['33'])).
% 1.74/1.96  thf('216', plain,
% 1.74/1.96      ((((k1_tarski @ sk_A) = (sk_B_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify', [status(thm)], ['35'])).
% 1.74/1.96  thf('217', plain,
% 1.74/1.96      ((((sk_C_1) != (sk_B_1))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('demod', [status(thm)], ['215', '216'])).
% 1.74/1.96  thf('218', plain,
% 1.74/1.96      ((((sk_C_1) = (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.74/1.96      inference('simplify_reflect-', [status(thm)], ['214', '217'])).
% 1.74/1.96  thf('219', plain,
% 1.74/1.96      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.74/1.96      inference('split', [status(esa)], ['37'])).
% 1.74/1.96  thf('220', plain,
% 1.74/1.96      ((((sk_C_1) != (sk_C_1)))
% 1.74/1.96         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))) & 
% 1.74/1.96             ~ (((sk_C_1) = (k1_xboole_0))))),
% 1.74/1.96      inference('sup-', [status(thm)], ['218', '219'])).
% 1.74/1.96  thf('221', plain,
% 1.74/1.96      ((((sk_C_1) = (k1_xboole_0))) | (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('simplify', [status(thm)], ['220'])).
% 1.74/1.96  thf('222', plain,
% 1.74/1.96      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.74/1.96      inference('split', [status(esa)], ['37'])).
% 1.74/1.96  thf('223', plain, ($false),
% 1.74/1.96      inference('sat_resolution*', [status(thm)],
% 1.74/1.96                ['40', '41', '43', '119', '221', '222'])).
% 1.74/1.96  
% 1.74/1.96  % SZS output end Refutation
% 1.74/1.96  
% 1.74/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
