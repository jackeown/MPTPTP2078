%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dvBOAwmJ9v

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:24 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 438 expanded)
%              Number of leaves         :   29 ( 130 expanded)
%              Depth                    :   20
%              Number of atoms          : 1074 (4880 expanded)
%              Number of equality atoms :  168 ( 935 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ( ( sk_B != k1_xboole_0 )
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
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X61: $i,X62: $i] :
      ( ( X62
        = ( k1_tarski @ X61 ) )
      | ( X62 = k1_xboole_0 )
      | ~ ( r1_tarski @ X62 @ ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','22'])).

thf('24',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r1_tarski @ X62 @ ( k1_tarski @ X63 ) )
      | ( X62 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('28',plain,(
    ! [X63: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X63 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('44',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
      = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('57',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('62',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
      = ( k4_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','66'])).

thf('68',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('72',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
        = sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('79',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('85',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('86',plain,
    ( ( sk_C_2 != sk_C_2 )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
    = sk_B ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C_2 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','87'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('89',plain,(
    ! [X32: $i] :
      ( ( k5_xboole_0 @ X32 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('90',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ X31 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('93',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('98',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('103',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X32: $i] :
      ( ( k5_xboole_0 @ X32 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('107',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','101','107'])).

thf('109',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('110',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('114',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('117',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['109','117'])).

thf('119',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['108','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','119'])).

thf('121',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','120'])).

thf('122',plain,(
    $false ),
    inference(simplify,[status(thm)],['121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dvBOAwmJ9v
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:32:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.94  % Solved by: fo/fo7.sh
% 0.74/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.94  % done 1397 iterations in 0.485s
% 0.74/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.94  % SZS output start Refutation
% 0.74/0.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.74/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.74/0.94  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.74/0.94  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.74/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.74/0.94  thf(t43_zfmisc_1, conjecture,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.74/0.94          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.74/0.94          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.74/0.94          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.74/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.94    (~( ![A:$i,B:$i,C:$i]:
% 0.74/0.94        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.74/0.94             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.74/0.94             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.74/0.94             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.74/0.94    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.74/0.94  thf('0', plain,
% 0.74/0.94      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('1', plain,
% 0.74/0.94      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.74/0.94         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.74/0.94      inference('split', [status(esa)], ['0'])).
% 0.74/0.94  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('3', plain,
% 0.74/0.94      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.74/0.94         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.74/0.94      inference('demod', [status(thm)], ['1', '2'])).
% 0.74/0.94  thf('4', plain,
% 0.74/0.94      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.74/0.94      inference('split', [status(esa)], ['0'])).
% 0.74/0.94  thf('5', plain,
% 0.74/0.94      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('6', plain,
% 0.74/0.94      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('split', [status(esa)], ['5'])).
% 0.74/0.94  thf(t7_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.94  thf('7', plain,
% 0.74/0.94      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.74/0.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.74/0.94  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(l3_zfmisc_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.74/0.94       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.74/0.94  thf('9', plain,
% 0.74/0.94      (![X61 : $i, X62 : $i]:
% 0.74/0.94         (((X62) = (k1_tarski @ X61))
% 0.74/0.94          | ((X62) = (k1_xboole_0))
% 0.74/0.94          | ~ (r1_tarski @ X62 @ (k1_tarski @ X61)))),
% 0.74/0.94      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.74/0.94  thf('10', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.74/0.94          | ((X0) = (k1_xboole_0))
% 0.74/0.94          | ((X0) = (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['8', '9'])).
% 0.74/0.94  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('12', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.74/0.94          | ((X0) = (k1_xboole_0))
% 0.74/0.94          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.74/0.94      inference('demod', [status(thm)], ['10', '11'])).
% 0.74/0.94  thf('13', plain,
% 0.74/0.94      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['7', '12'])).
% 0.74/0.94  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('15', plain,
% 0.74/0.94      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('16', plain,
% 0.74/0.94      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.74/0.94      inference('split', [status(esa)], ['15'])).
% 0.74/0.94  thf('17', plain,
% 0.74/0.94      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.74/0.94         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.74/0.94      inference('sup-', [status(thm)], ['14', '16'])).
% 0.74/0.94  thf('18', plain,
% 0.74/0.94      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.74/0.94         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.74/0.94      inference('sup-', [status(thm)], ['13', '17'])).
% 0.74/0.94  thf('19', plain,
% 0.74/0.94      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.74/0.94      inference('simplify', [status(thm)], ['18'])).
% 0.74/0.94  thf('20', plain,
% 0.74/0.94      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.74/0.94      inference('split', [status(esa)], ['0'])).
% 0.74/0.94  thf('21', plain,
% 0.74/0.94      ((((sk_B) != (sk_B)))
% 0.74/0.94         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.74/0.94      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/0.94  thf('22', plain,
% 0.74/0.94      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('simplify', [status(thm)], ['21'])).
% 0.74/0.94  thf('23', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 0.74/0.94  thf('24', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.74/0.94  thf(d3_tarski, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( r1_tarski @ A @ B ) <=>
% 0.74/0.94       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.74/0.94  thf('25', plain,
% 0.74/0.94      (![X5 : $i, X7 : $i]:
% 0.74/0.94         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.74/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.94  thf('26', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('27', plain,
% 0.74/0.94      (![X62 : $i, X63 : $i]:
% 0.74/0.94         ((r1_tarski @ X62 @ (k1_tarski @ X63)) | ((X62) != (k1_xboole_0)))),
% 0.74/0.94      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.74/0.94  thf('28', plain,
% 0.74/0.94      (![X63 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X63))),
% 0.74/0.94      inference('simplify', [status(thm)], ['27'])).
% 0.74/0.94  thf('29', plain, ((r1_tarski @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('sup+', [status(thm)], ['26', '28'])).
% 0.74/0.94  thf(t28_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.74/0.94  thf('30', plain,
% 0.74/0.94      (![X21 : $i, X22 : $i]:
% 0.74/0.94         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.74/0.94      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.74/0.94  thf('31', plain,
% 0.74/0.94      (((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.74/0.94         = (k1_xboole_0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.94  thf(t4_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.94            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.94       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.74/0.94            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.74/0.94  thf('32', plain,
% 0.74/0.94      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.74/0.94         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.74/0.94          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.74/0.94      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.74/0.94  thf('33', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.74/0.94          | ~ (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['31', '32'])).
% 0.74/0.94  thf('34', plain,
% 0.74/0.94      (((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.74/0.94         = (k1_xboole_0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.94  thf(d7_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.74/0.94       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.74/0.94  thf('35', plain,
% 0.74/0.94      (![X8 : $i, X10 : $i]:
% 0.74/0.94         ((r1_xboole_0 @ X8 @ X10)
% 0.74/0.94          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.74/0.94      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.74/0.94  thf('36', plain,
% 0.74/0.94      ((((k1_xboole_0) != (k1_xboole_0))
% 0.74/0.94        | (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['34', '35'])).
% 0.74/0.94  thf('37', plain,
% 0.74/0.94      ((r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('simplify', [status(thm)], ['36'])).
% 0.74/0.94  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.74/0.94      inference('demod', [status(thm)], ['33', '37'])).
% 0.74/0.94  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.74/0.94      inference('sup-', [status(thm)], ['25', '38'])).
% 0.74/0.94  thf(t12_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.74/0.94  thf('40', plain,
% 0.74/0.94      (![X19 : $i, X20 : $i]:
% 0.74/0.94         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.74/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.74/0.94  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['39', '40'])).
% 0.74/0.94  thf('42', plain,
% 0.74/0.94      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['7', '12'])).
% 0.74/0.94  thf(l98_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( k5_xboole_0 @ A @ B ) =
% 0.74/0.94       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.74/0.94  thf('43', plain,
% 0.74/0.94      (![X15 : $i, X16 : $i]:
% 0.74/0.94         ((k5_xboole_0 @ X15 @ X16)
% 0.74/0.94           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 0.74/0.94              (k3_xboole_0 @ X15 @ X16)))),
% 0.74/0.94      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.74/0.94  thf('44', plain,
% 0.74/0.94      ((((k5_xboole_0 @ sk_B @ sk_C_2)
% 0.74/0.94          = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C_2)))
% 0.74/0.94        | ((sk_B) = (k1_xboole_0)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['42', '43'])).
% 0.74/0.94  thf('45', plain,
% 0.74/0.94      (![X5 : $i, X7 : $i]:
% 0.74/0.94         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.74/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.94  thf('46', plain,
% 0.74/0.94      (![X5 : $i, X7 : $i]:
% 0.74/0.94         ((r1_tarski @ X5 @ X7) | ~ (r2_hidden @ (sk_C @ X7 @ X5) @ X7))),
% 0.74/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.94  thf('47', plain,
% 0.74/0.94      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['45', '46'])).
% 0.74/0.94  thf('48', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.74/0.94      inference('simplify', [status(thm)], ['47'])).
% 0.74/0.94  thf('49', plain,
% 0.74/0.94      (![X19 : $i, X20 : $i]:
% 0.74/0.94         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.74/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.74/0.94  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['48', '49'])).
% 0.74/0.94  thf(t29_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.74/0.94  thf('51', plain,
% 0.74/0.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.74/0.94         (r1_tarski @ (k3_xboole_0 @ X23 @ X24) @ (k2_xboole_0 @ X23 @ X25))),
% 0.74/0.94      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.74/0.94  thf('52', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.74/0.94      inference('sup+', [status(thm)], ['50', '51'])).
% 0.74/0.94  thf('53', plain,
% 0.74/0.94      (![X19 : $i, X20 : $i]:
% 0.74/0.94         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 0.74/0.94      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.74/0.94  thf('54', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['52', '53'])).
% 0.74/0.94  thf('55', plain,
% 0.74/0.94      (![X15 : $i, X16 : $i]:
% 0.74/0.94         ((k5_xboole_0 @ X15 @ X16)
% 0.74/0.94           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 0.74/0.94              (k3_xboole_0 @ X15 @ X16)))),
% 0.74/0.94      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.74/0.94  thf('56', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.74/0.94           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['54', '55'])).
% 0.74/0.94  thf(commutativity_k5_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.74/0.94  thf('57', plain,
% 0.74/0.94      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.74/0.94  thf(t100_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.74/0.94  thf('58', plain,
% 0.74/0.94      (![X17 : $i, X18 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X17 @ X18)
% 0.74/0.94           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.94  thf(commutativity_k3_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.74/0.94  thf('59', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/0.94  thf('60', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X0 @ X1)
% 0.74/0.94           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))))),
% 0.74/0.94      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.74/0.94  thf('61', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.74/0.94      inference('sup+', [status(thm)], ['50', '51'])).
% 0.74/0.94  thf('62', plain,
% 0.74/0.94      (![X21 : $i, X22 : $i]:
% 0.74/0.94         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.74/0.94      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.74/0.94  thf('63', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.74/0.94           = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('sup-', [status(thm)], ['61', '62'])).
% 0.74/0.94  thf('64', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/0.94  thf('65', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.74/0.94           = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('demod', [status(thm)], ['63', '64'])).
% 0.74/0.94  thf('66', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X0 @ X1)
% 0.74/0.94           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.74/0.94      inference('demod', [status(thm)], ['60', '65'])).
% 0.74/0.94  thf('67', plain,
% 0.74/0.94      ((((k5_xboole_0 @ sk_B @ sk_C_2) = (k4_xboole_0 @ sk_B @ sk_C_2))
% 0.74/0.94        | ((sk_B) = (k1_xboole_0)))),
% 0.74/0.94      inference('demod', [status(thm)], ['44', '66'])).
% 0.74/0.94  thf('68', plain,
% 0.74/0.94      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.74/0.94         (r1_tarski @ (k3_xboole_0 @ X23 @ X24) @ (k2_xboole_0 @ X23 @ X25))),
% 0.74/0.94      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.74/0.94  thf('69', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.74/0.94          | ((X0) = (k1_xboole_0))
% 0.74/0.94          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.74/0.94      inference('demod', [status(thm)], ['10', '11'])).
% 0.74/0.94  thf('70', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (((k3_xboole_0 @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.74/0.94          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['68', '69'])).
% 0.74/0.94  thf('71', plain,
% 0.74/0.94      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.74/0.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.74/0.94  thf('72', plain,
% 0.74/0.94      (![X21 : $i, X22 : $i]:
% 0.74/0.94         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.74/0.94      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.74/0.94  thf('73', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.74/0.94      inference('sup-', [status(thm)], ['71', '72'])).
% 0.74/0.94  thf('74', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ X0)) = (sk_B))
% 0.74/0.94          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['70', '73'])).
% 0.74/0.94  thf('75', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.74/0.94           = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('demod', [status(thm)], ['63', '64'])).
% 0.74/0.94  thf('76', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (((k3_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.74/0.94          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.74/0.94      inference('demod', [status(thm)], ['74', '75'])).
% 0.74/0.94  thf('77', plain,
% 0.74/0.94      (![X17 : $i, X18 : $i]:
% 0.74/0.94         ((k4_xboole_0 @ X17 @ X18)
% 0.74/0.94           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.94  thf('78', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (((k4_xboole_0 @ sk_B @ X0) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 0.74/0.94          | ((k3_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['76', '77'])).
% 0.74/0.94  thf(t5_boole, axiom,
% 0.74/0.94    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.74/0.94  thf('79', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.74/0.94      inference('cnf', [status(esa)], [t5_boole])).
% 0.74/0.94  thf('80', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (((k4_xboole_0 @ sk_B @ X0) = (sk_B))
% 0.74/0.94          | ((k3_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.74/0.94      inference('demod', [status(thm)], ['78', '79'])).
% 0.74/0.94  thf('81', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.74/0.94  thf('82', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['52', '53'])).
% 0.74/0.94  thf('83', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.74/0.94      inference('sup+', [status(thm)], ['81', '82'])).
% 0.74/0.94  thf('84', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (((k2_xboole_0 @ sk_B @ X0) = (X0))
% 0.74/0.94          | ((k4_xboole_0 @ sk_B @ X0) = (sk_B)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['80', '83'])).
% 0.74/0.94  thf('85', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.94      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.74/0.94  thf('86', plain,
% 0.74/0.94      ((((sk_C_2) != (sk_C_2)) | ((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['84', '85'])).
% 0.74/0.94  thf('87', plain, (((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))),
% 0.74/0.94      inference('simplify', [status(thm)], ['86'])).
% 0.74/0.94  thf('88', plain,
% 0.74/0.94      ((((k5_xboole_0 @ sk_B @ sk_C_2) = (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.74/0.94      inference('demod', [status(thm)], ['67', '87'])).
% 0.74/0.94  thf(t92_xboole_1, axiom,
% 0.74/0.94    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.74/0.94  thf('89', plain, (![X32 : $i]: ((k5_xboole_0 @ X32 @ X32) = (k1_xboole_0))),
% 0.74/0.94      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.74/0.94  thf(t91_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.74/0.94       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.74/0.94  thf('90', plain,
% 0.74/0.94      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.74/0.94         ((k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ X31)
% 0.74/0.94           = (k5_xboole_0 @ X29 @ (k5_xboole_0 @ X30 @ X31)))),
% 0.74/0.94      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.74/0.94  thf('91', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.74/0.94           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.74/0.94      inference('sup+', [status(thm)], ['89', '90'])).
% 0.74/0.94  thf('92', plain,
% 0.74/0.94      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.74/0.94  thf('93', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.74/0.94      inference('cnf', [status(esa)], [t5_boole])).
% 0.74/0.94  thf('94', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.74/0.94      inference('sup+', [status(thm)], ['92', '93'])).
% 0.74/0.94  thf('95', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.74/0.94      inference('demod', [status(thm)], ['91', '94'])).
% 0.74/0.94  thf('96', plain,
% 0.74/0.94      ((((sk_C_2) = (k5_xboole_0 @ sk_B @ sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.74/0.95      inference('sup+', [status(thm)], ['88', '95'])).
% 0.74/0.95  thf('97', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.74/0.95      inference('simplify', [status(thm)], ['47'])).
% 0.74/0.95  thf('98', plain,
% 0.74/0.95      (![X21 : $i, X22 : $i]:
% 0.74/0.95         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.74/0.95      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.74/0.95  thf('99', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['97', '98'])).
% 0.74/0.95  thf('100', plain,
% 0.74/0.95      (![X17 : $i, X18 : $i]:
% 0.74/0.95         ((k4_xboole_0 @ X17 @ X18)
% 0.74/0.95           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.74/0.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.95  thf('101', plain,
% 0.74/0.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.74/0.95      inference('sup+', [status(thm)], ['99', '100'])).
% 0.74/0.95  thf('102', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['48', '49'])).
% 0.74/0.95  thf('103', plain,
% 0.74/0.95      (![X15 : $i, X16 : $i]:
% 0.74/0.95         ((k5_xboole_0 @ X15 @ X16)
% 0.74/0.95           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 0.74/0.95              (k3_xboole_0 @ X15 @ X16)))),
% 0.74/0.95      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.74/0.95  thf('104', plain,
% 0.74/0.95      (![X0 : $i]:
% 0.74/0.95         ((k5_xboole_0 @ X0 @ X0)
% 0.74/0.95           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.74/0.95      inference('sup+', [status(thm)], ['102', '103'])).
% 0.74/0.95  thf('105', plain, (![X32 : $i]: ((k5_xboole_0 @ X32 @ X32) = (k1_xboole_0))),
% 0.74/0.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.74/0.95  thf('106', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['97', '98'])).
% 0.74/0.95  thf('107', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.74/0.95      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.74/0.95  thf('108', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.74/0.95      inference('demod', [status(thm)], ['96', '101', '107'])).
% 0.74/0.95  thf('109', plain,
% 0.74/0.95      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.74/0.95      inference('split', [status(esa)], ['15'])).
% 0.74/0.95  thf('110', plain,
% 0.74/0.95      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.74/0.95      inference('simplify', [status(thm)], ['18'])).
% 0.74/0.95  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.74/0.95      inference('sup-', [status(thm)], ['39', '40'])).
% 0.74/0.95  thf('112', plain,
% 0.74/0.95      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.74/0.95         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.74/0.95      inference('sup+', [status(thm)], ['110', '111'])).
% 0.74/0.95  thf('113', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.74/0.95      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.74/0.95  thf('114', plain,
% 0.74/0.95      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.74/0.95      inference('sup-', [status(thm)], ['112', '113'])).
% 0.74/0.95  thf('115', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.74/0.95      inference('simplify', [status(thm)], ['114'])).
% 0.74/0.95  thf('116', plain,
% 0.74/0.95      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.74/0.95      inference('split', [status(esa)], ['15'])).
% 0.74/0.95  thf('117', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.74/0.95      inference('sat_resolution*', [status(thm)], ['115', '116'])).
% 0.74/0.95  thf('118', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.74/0.95      inference('simpl_trail', [status(thm)], ['109', '117'])).
% 0.74/0.95  thf('119', plain, (((sk_B) = (k1_xboole_0))),
% 0.74/0.95      inference('simplify_reflect-', [status(thm)], ['108', '118'])).
% 0.74/0.95  thf('120', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.74/0.95      inference('demod', [status(thm)], ['41', '119'])).
% 0.74/0.95  thf('121', plain, (((sk_C_2) != (sk_C_2))),
% 0.74/0.95      inference('demod', [status(thm)], ['24', '120'])).
% 0.74/0.95  thf('122', plain, ($false), inference('simplify', [status(thm)], ['121'])).
% 0.74/0.95  
% 0.74/0.95  % SZS output end Refutation
% 0.74/0.95  
% 0.74/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
