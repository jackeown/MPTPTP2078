%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R5h9UvLU8a

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:10 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 194 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  558 (1519 expanded)
%              Number of equality atoms :  102 ( 254 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X20 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ~ ( r2_hidden @ X20 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 != X15 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X15 ) )
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) )
        = X23 )
      | ( r2_hidden @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','28'])).

thf('30',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X32 @ X30 )
      | ( ( sk_B @ X30 )
       != ( k4_tarski @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','17'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('39',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X27: $i,X29: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X27 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('41',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('43',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ( ( sk_B @ X30 )
       != ( k4_tarski @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['27'])).

thf('55',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','55'])).

thf('57',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('58',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R5h9UvLU8a
% 0.15/0.39  % Computer   : n016.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.24/0.39  % CPULimit   : 60
% 0.24/0.39  % DateTime   : Tue Dec  1 17:39:19 EST 2020
% 0.24/0.39  % CPUTime    : 
% 0.24/0.39  % Running portfolio for 600 s
% 0.24/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.24/0.39  % Number of cores: 8
% 0.24/0.39  % Python version: Python 3.6.8
% 0.24/0.40  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 121 iterations in 0.047s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(t9_mcart_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ![B:$i]:
% 0.37/0.55            ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.55                 ( ![C:$i,D:$i]:
% 0.37/0.55                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.37/0.55                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (![X30 : $i]:
% 0.37/0.55         (((X30) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X30) @ X30))),
% 0.37/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.55  thf(t20_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.55         ( k1_tarski @ A ) ) <=>
% 0.37/0.55       ( ( A ) != ( B ) ) ))).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.37/0.55            = (k1_tarski @ X16))
% 0.37/0.55          | ((X16) = (X17)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.55  thf(t64_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.37/0.55       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.55         (((X18) != (X20))
% 0.37/0.55          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20))))),
% 0.37/0.55      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X19 : $i, X20 : $i]:
% 0.37/0.55         ~ (r2_hidden @ X20 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '3'])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.55          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i]:
% 0.37/0.55         (((X16) != (X15))
% 0.37/0.55          | ((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X15))
% 0.37/0.55              != (k1_tarski @ X16)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X15 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X15))
% 0.37/0.55           != (k1_tarski @ X15))),
% 0.37/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.55  thf('8', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf(t100_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X15 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X15))
% 0.37/0.55           != (k1_tarski @ X15))),
% 0.37/0.55      inference('demod', [status(thm)], ['7', '10'])).
% 0.37/0.55  thf(t21_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i]:
% 0.37/0.55         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X1 @ X2)
% 0.37/0.55           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.37/0.55           = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf(t46_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.37/0.55  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '16'])).
% 0.37/0.55  thf('18', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.37/0.55      inference('clc', [status(thm)], ['5', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.55  thf(t65_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.37/0.55       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X23 : $i, X24 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ X23 @ (k1_tarski @ X24)) = (X23))
% 0.37/0.55          | (r2_hidden @ X24 @ X23))),
% 0.37/0.55      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.37/0.55            = (k1_tarski @ X0))
% 0.37/0.55          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X15 : $i]:
% 0.37/0.55         ((k5_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X15))
% 0.37/0.55           != (k1_tarski @ X15))),
% 0.37/0.55      inference('demod', [status(thm)], ['7', '10'])).
% 0.37/0.55  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf(t20_mcart_1, conjecture,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.55       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i]:
% 0.37/0.55        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.55          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.37/0.55  thf('24', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t7_mcart_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.37/0.55       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X27 : $i, X28 : $i]: ((k1_mcart_1 @ (k4_tarski @ X27 @ X28)) = (X27))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.55  thf('26', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['24', '25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['26', '28'])).
% 0.37/0.55  thf('30', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.37/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['29', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.55         (((X30) = (k1_xboole_0))
% 0.37/0.55          | ~ (r2_hidden @ X32 @ X30)
% 0.37/0.55          | ((sk_B @ X30) != (k4_tarski @ X32 @ X31)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (((sk_B @ X0) != (sk_A))
% 0.37/0.55           | ~ (r2_hidden @ sk_A @ X0)
% 0.37/0.55           | ((X0) = (k1_xboole_0))))
% 0.37/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.37/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['23', '33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['18', '34'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['35'])).
% 0.37/0.55  thf('37', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.37/0.55      inference('clc', [status(thm)], ['5', '17'])).
% 0.37/0.55  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.37/0.55  thf('39', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (![X27 : $i, X29 : $i]: ((k2_mcart_1 @ (k4_tarski @ X27 @ X29)) = (X29))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.55  thf('41', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.37/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['27'])).
% 0.37/0.55  thf('43', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.55  thf('44', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.37/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.37/0.55  thf('46', plain,
% 0.37/0.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.55         (((X30) = (k1_xboole_0))
% 0.37/0.55          | ~ (r2_hidden @ X31 @ X30)
% 0.37/0.55          | ((sk_B @ X30) != (k4_tarski @ X32 @ X31)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (((sk_B @ X0) != (sk_A))
% 0.37/0.55           | ~ (r2_hidden @ sk_A @ X0)
% 0.37/0.55           | ((X0) = (k1_xboole_0))))
% 0.37/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.37/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['38', '47'])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['37', '48'])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['49'])).
% 0.37/0.55  thf('51', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '16'])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.55  thf('53', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.37/0.55  thf('54', plain,
% 0.37/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['27'])).
% 0.37/0.55  thf('55', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('56', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['36', '55'])).
% 0.37/0.55  thf('57', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.37/0.55      inference('demod', [status(thm)], ['11', '16'])).
% 0.37/0.55  thf('58', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.55  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
