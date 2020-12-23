%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rSrYKmjdjr

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:31 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 559 expanded)
%              Number of leaves         :   24 ( 151 expanded)
%              Depth                    :   19
%              Number of atoms          :  610 (7090 expanded)
%              Number of equality atoms :  108 (1506 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    | ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_3
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k4_xboole_0 @ X31 @ ( k4_xboole_0 @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X28: $i] :
      ( ( k3_xboole_0 @ X28 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X33: $i] :
      ( ( k5_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('20',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46
        = ( k1_tarski @ X45 ) )
      | ( X46 = k1_xboole_0 )
      | ~ ( r1_tarski @ X46 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_3 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_3 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('30',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ( X18 != X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X19: $i] :
      ( r1_tarski @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_tarski @ X23 @ ( k2_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('37',plain,
    ( ( sk_C_3
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_C_3
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( sk_C_3
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( sk_C_3 != sk_C_3 )
      | ( sk_C_3 = k1_xboole_0 ) )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( sk_C_3 = k1_xboole_0 )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_C_3 != k1_xboole_0 )
   <= ( sk_C_3 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('44',plain,
    ( ( sk_C_3 != sk_C_3 )
   <= ( ( sk_C_3
       != ( k1_tarski @ sk_A ) )
      & ( sk_C_3 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( sk_C_3
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_B_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['29','31','45'])).

thf('47',plain,(
    sk_B_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference(simpl_trail,[status(thm)],['28','46'])).

thf('48',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['24','47'])).

thf('49',plain,
    ( ( sk_C_3 = k1_xboole_0 )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('50',plain,
    ( ( sk_C_3 = sk_B_1 )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['24','47'])).

thf('52',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_C_3
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    sk_C_3
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_C_3 = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['50','56'])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_C_3 = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['50','56'])).

thf('60',plain,(
    ! [X19: $i] :
      ( r1_tarski @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('61',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_xboole_0 @ X27 @ X26 )
        = X26 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','57','58','59','62'])).

thf('64',plain,
    ( $false
   <= ( sk_C_3
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_C_3
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('66',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rSrYKmjdjr
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 858 iterations in 0.312s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.78  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.59/0.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(t43_zfmisc_1, conjecture,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.59/0.78          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.59/0.78          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.59/0.78          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.78        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.59/0.78             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.59/0.78             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.59/0.78             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_3) != (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      ((((sk_C_3) != (k1_tarski @ sk_A)))
% 0.59/0.78         <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['0'])).
% 0.59/0.78  thf(t46_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X29 : $i, X30 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ X29 @ (k2_xboole_0 @ X29 @ X30)) = (k1_xboole_0))),
% 0.59/0.78      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.59/0.78  thf(t48_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X31 : $i, X32 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ X31 @ (k4_xboole_0 @ X31 @ X32))
% 0.59/0.78           = (k3_xboole_0 @ X31 @ X32))),
% 0.59/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.59/0.78           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['2', '3'])).
% 0.59/0.78  thf(t2_boole, axiom,
% 0.59/0.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X28 : $i]: ((k3_xboole_0 @ X28 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.59/0.78  thf(t100_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      (![X21 : $i, X22 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ X21 @ X22)
% 0.59/0.78           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['5', '6'])).
% 0.59/0.78  thf(t5_boole, axiom,
% 0.59/0.78    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.78  thf('8', plain, (![X33 : $i]: ((k5_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 0.59/0.78      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.78  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['7', '8'])).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.78      inference('demod', [status(thm)], ['4', '9'])).
% 0.59/0.78  thf(d3_tarski, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      (![X1 : $i, X3 : $i]:
% 0.59/0.78         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.78  thf(d4_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.59/0.78       ( ![D:$i]:
% 0.59/0.78         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.78           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X8 @ X7)
% 0.59/0.78          | (r2_hidden @ X8 @ X6)
% 0.59/0.78          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.59/0.78         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['12'])).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.59/0.78          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '13'])).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      (![X1 : $i, X3 : $i]:
% 0.59/0.78         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.78      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.59/0.78          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.59/0.78      inference('simplify', [status(thm)], ['16'])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.78      inference('sup+', [status(thm)], ['10', '17'])).
% 0.59/0.78  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(l3_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.59/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X45 : $i, X46 : $i]:
% 0.59/0.78         (((X46) = (k1_tarski @ X45))
% 0.59/0.78          | ((X46) = (k1_xboole_0))
% 0.59/0.78          | ~ (r1_tarski @ X46 @ (k1_tarski @ X45)))),
% 0.59/0.78      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3))
% 0.59/0.78          | ((X0) = (k1_xboole_0))
% 0.59/0.78          | ((X0) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.78  thf('22', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3))
% 0.59/0.78          | ((X0) = (k1_xboole_0))
% 0.59/0.78          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_3)))),
% 0.59/0.78      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))
% 0.59/0.78        | ((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['18', '23'])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_3) != (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.59/0.78         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['25'])).
% 0.59/0.78  thf('27', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_3)))
% 0.59/0.78         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('demod', [status(thm)], ['26', '27'])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (~ (((sk_B_1) = (k1_tarski @ sk_A))) | ~ (((sk_C_3) = (k1_xboole_0)))),
% 0.59/0.78      inference('split', [status(esa)], ['25'])).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_3) != (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      (~ (((sk_B_1) = (k1_tarski @ sk_A))) | 
% 0.59/0.78       ~ (((sk_C_3) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('split', [status(esa)], ['30'])).
% 0.59/0.78  thf(d10_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X18 : $i, X19 : $i]: ((r1_tarski @ X18 @ X19) | ((X18) != (X19)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.78  thf('33', plain, (![X19 : $i]: (r1_tarski @ X19 @ X19)),
% 0.59/0.78      inference('simplify', [status(thm)], ['32'])).
% 0.59/0.78  thf(t10_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.59/0.78  thf('34', plain,
% 0.59/0.78      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X23 @ X24)
% 0.59/0.78          | (r1_tarski @ X23 @ (k2_xboole_0 @ X25 @ X24)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.59/0.78  thf('35', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_3))
% 0.59/0.78          | ((X0) = (k1_xboole_0))
% 0.59/0.78          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_3)))),
% 0.59/0.78      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      ((((sk_C_3) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))
% 0.59/0.78        | ((sk_C_3) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.78  thf('38', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      ((((sk_C_3) != (k1_tarski @ sk_A)))
% 0.59/0.78         <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('split', [status(esa)], ['0'])).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      ((((sk_C_3) != (k2_xboole_0 @ sk_B_1 @ sk_C_3)))
% 0.59/0.78         <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (((((sk_C_3) != (sk_C_3)) | ((sk_C_3) = (k1_xboole_0))))
% 0.59/0.78         <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['37', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      ((((sk_C_3) = (k1_xboole_0))) <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      ((((sk_C_3) != (k1_xboole_0))) <= (~ (((sk_C_3) = (k1_xboole_0))))),
% 0.59/0.78      inference('split', [status(esa)], ['25'])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      ((((sk_C_3) != (sk_C_3)))
% 0.59/0.78         <= (~ (((sk_C_3) = (k1_tarski @ sk_A))) & 
% 0.59/0.78             ~ (((sk_C_3) = (k1_xboole_0))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.78  thf('45', plain,
% 0.59/0.78      ((((sk_C_3) = (k1_xboole_0))) | (((sk_C_3) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['44'])).
% 0.59/0.78  thf('46', plain, (~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['29', '31', '45'])).
% 0.59/0.78  thf('47', plain, (((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['28', '46'])).
% 0.59/0.78  thf('48', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['24', '47'])).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      ((((sk_C_3) = (k1_xboole_0))) <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.78  thf('50', plain,
% 0.59/0.78      ((((sk_C_3) = (sk_B_1))) <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['48', '49'])).
% 0.59/0.78  thf('51', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['24', '47'])).
% 0.59/0.78  thf('52', plain,
% 0.59/0.78      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.59/0.78      inference('split', [status(esa)], ['0'])).
% 0.59/0.78  thf('53', plain,
% 0.59/0.78      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.78  thf('54', plain, ((((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.78  thf('55', plain,
% 0.59/0.78      (~ (((sk_C_3) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.59/0.78      inference('split', [status(esa)], ['0'])).
% 0.59/0.78  thf('56', plain, (~ (((sk_C_3) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.59/0.78  thf('57', plain, (((sk_C_3) = (sk_B_1))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['50', '56'])).
% 0.59/0.78  thf('58', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_3))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('59', plain, (((sk_C_3) = (sk_B_1))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['50', '56'])).
% 0.59/0.78  thf('60', plain, (![X19 : $i]: (r1_tarski @ X19 @ X19)),
% 0.59/0.78      inference('simplify', [status(thm)], ['32'])).
% 0.59/0.78  thf(t12_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.59/0.78  thf('61', plain,
% 0.59/0.78      (![X26 : $i, X27 : $i]:
% 0.59/0.78         (((k2_xboole_0 @ X27 @ X26) = (X26)) | ~ (r1_tarski @ X27 @ X26))),
% 0.59/0.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.78  thf('62', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.78  thf('63', plain,
% 0.59/0.78      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('demod', [status(thm)], ['1', '57', '58', '59', '62'])).
% 0.59/0.78  thf('64', plain, (($false) <= (~ (((sk_C_3) = (k1_tarski @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['63'])).
% 0.59/0.78  thf('65', plain, (~ (((sk_C_3) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.59/0.78  thf('66', plain, ($false),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['64', '65'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
