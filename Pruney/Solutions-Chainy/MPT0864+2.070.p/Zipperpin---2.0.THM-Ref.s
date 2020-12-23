%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J2K7PeEhux

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 305 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   21
%              Number of atoms          :  612 (2537 expanded)
%              Number of equality atoms :  106 ( 351 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
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
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('7',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 != X15 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X15 ) )
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('11',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['9','27'])).

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

thf('29',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('31',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X29 @ X27 )
      | ( ( sk_B @ X27 )
       != ( k4_tarski @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['9','27'])).

thf('41',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('43',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('45',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ( ( sk_B @ X27 )
       != ( k4_tarski @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf('52',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_A ) )
     != sk_A )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','52'])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('59',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_A )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['38','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['28','60'])).

thf('62',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf('63',plain,(
    ( sk_B @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','63'])).

thf('65',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['15','26'])).

thf('67',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J2K7PeEhux
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 157 iterations in 0.078s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(t9_mcart_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.53                 ( ![C:$i,D:$i]:
% 0.21/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.53                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X27 : $i]:
% 0.21/0.53         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.53  thf(t20_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.53         ( k1_tarski @ A ) ) <=>
% 0.21/0.53       ( ( A ) != ( B ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.21/0.53            = (k1_tarski @ X16))
% 0.21/0.53          | ((X16) = (X17)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.53  thf(t64_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.53       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.53         (((X18) != (X20))
% 0.21/0.53          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20))))),
% 0.21/0.53      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         ~ (r2_hidden @ X20 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.53          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.53          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X27 : $i]:
% 0.21/0.53         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.21/0.53          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.53          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.53          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i]:
% 0.21/0.53         (((X16) != (X15))
% 0.21/0.53          | ((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X15))
% 0.21/0.53              != (k1_tarski @ X16)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X15 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X15))
% 0.21/0.53           != (k1_tarski @ X15))),
% 0.21/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.53  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.53  thf('12', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.21/0.53      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.53  thf(t100_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X7 @ X8)
% 0.21/0.53           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X15 : $i]:
% 0.21/0.53         ((k5_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X15))
% 0.21/0.53           != (k1_tarski @ X15))),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X27 : $i]:
% 0.21/0.53         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf(d5_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.53       ( ![D:$i]:
% 0.21/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.53          | (r2_hidden @ X4 @ X1)
% 0.21/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.53         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.53          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.53          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.21/0.53          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['20', '24'])).
% 0.21/0.53  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '25'])).
% 0.21/0.53  thf('27', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '26'])).
% 0.21/0.53  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['9', '27'])).
% 0.21/0.53  thf(t20_mcart_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.53       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.53          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.21/0.53  thf('29', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t7_mcart_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.53  thf('31', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['31', '33'])).
% 0.21/0.53  thf('35', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.21/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.53         (((X27) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X29 @ X27)
% 0.21/0.53          | ((sk_B @ X27) != (k4_tarski @ X29 @ X28)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (((sk_B @ X0) != (sk_A))
% 0.21/0.53           | ~ (r2_hidden @ sk_A @ X0)
% 0.21/0.53           | ((X0) = (k1_xboole_0))))
% 0.21/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.53          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '4'])).
% 0.21/0.53  thf('40', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.53      inference('clc', [status(thm)], ['9', '27'])).
% 0.21/0.53  thf('41', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.53  thf('43', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.21/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['32'])).
% 0.21/0.53  thf('45', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.53  thf('46', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.53         (((X27) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X28 @ X27)
% 0.21/0.53          | ((sk_B @ X27) != (k4_tarski @ X29 @ X28)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      ((![X0 : $i]:
% 0.21/0.53          (((sk_B @ X0) != (sk_A))
% 0.21/0.53           | ~ (r2_hidden @ sk_A @ X0)
% 0.21/0.53           | ((X0) = (k1_xboole_0))))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.53         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '49'])).
% 0.21/0.53  thf('51', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.21/0.53      inference('demod', [status(thm)], ['15', '26'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((((sk_B @ (k1_tarski @ sk_A)) != (sk_A)))
% 0.21/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.53      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.21/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '52'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.54  thf('55', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '26'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['32'])).
% 0.21/0.54  thf('59', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((sk_B @ X0) != (sk_A))
% 0.21/0.54          | ~ (r2_hidden @ sk_A @ X0)
% 0.21/0.54          | ((X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['38', '59'])).
% 0.21/0.54  thf('61', plain,
% 0.21/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.54        | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '60'])).
% 0.21/0.54  thf('62', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '26'])).
% 0.21/0.54  thf('63', plain, (((sk_B @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['61', '62'])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '63'])).
% 0.21/0.54  thf('65', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.54  thf('66', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '26'])).
% 0.21/0.54  thf('67', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.54  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
