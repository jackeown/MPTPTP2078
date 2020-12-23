%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xWrRgb3Oh3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:36 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  572 ( 955 expanded)
%              Number of equality atoms :   64 ( 109 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X23 @ X20 ) @ ( sk_C_1 @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C_1 @ X1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X23
        = ( k2_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ ( sk_C_1 @ X23 @ X20 ) ) @ X20 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X1 = k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t195_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
                = A )
              & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
                = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t195_relat_1])).

thf('13',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_A )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_B_1 )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_B_1 ) ),
    inference(split,[status(esa)],['13'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X16 @ X13 ) @ ( sk_D @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X13: $i,X16: $i,X17: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X16 @ X13 ) @ X17 ) @ X13 )
      | ~ ( r2_hidden @ ( sk_C @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_A )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_B_1 )
    | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('34',plain,(
    ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
 != sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
 != sk_B_1 ),
    inference(simpl_trail,[status(thm)],['14','34'])).

thf('36',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','35'])).

thf('37',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xWrRgb3Oh3
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.28/1.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.28/1.45  % Solved by: fo/fo7.sh
% 1.28/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.45  % done 335 iterations in 1.004s
% 1.28/1.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.28/1.45  % SZS output start Refutation
% 1.28/1.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.28/1.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.28/1.45  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.28/1.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.28/1.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.28/1.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.28/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.45  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.28/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.28/1.45  thf(sk_B_type, type, sk_B: $i > $i).
% 1.28/1.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.28/1.45  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.28/1.45  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.28/1.45  thf(t7_xboole_0, axiom,
% 1.28/1.45    (![A:$i]:
% 1.28/1.45     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.28/1.45          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.28/1.45  thf('0', plain,
% 1.28/1.45      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.28/1.45      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.28/1.45  thf(d5_relat_1, axiom,
% 1.28/1.45    (![A:$i,B:$i]:
% 1.28/1.45     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.28/1.45       ( ![C:$i]:
% 1.28/1.45         ( ( r2_hidden @ C @ B ) <=>
% 1.28/1.45           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.28/1.45  thf('1', plain,
% 1.28/1.45      (![X20 : $i, X23 : $i]:
% 1.28/1.45         (((X23) = (k2_relat_1 @ X20))
% 1.28/1.45          | (r2_hidden @ 
% 1.28/1.45             (k4_tarski @ (sk_D_2 @ X23 @ X20) @ (sk_C_1 @ X23 @ X20)) @ X20)
% 1.28/1.45          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 1.28/1.45      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.28/1.45  thf(l54_zfmisc_1, axiom,
% 1.28/1.45    (![A:$i,B:$i,C:$i,D:$i]:
% 1.28/1.45     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.28/1.45       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.28/1.45  thf('2', plain,
% 1.28/1.45      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.28/1.45         ((r2_hidden @ X3 @ X4)
% 1.28/1.45          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X4)))),
% 1.28/1.45      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.28/1.45  thf('3', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.45         ((r2_hidden @ (sk_C_1 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 1.28/1.45          | ((X2) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.28/1.45          | (r2_hidden @ (sk_C_1 @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 1.28/1.45      inference('sup-', [status(thm)], ['1', '2'])).
% 1.28/1.45  thf('4', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         ((r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 1.28/1.45          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.28/1.45      inference('eq_fact', [status(thm)], ['3'])).
% 1.28/1.45  thf('5', plain,
% 1.28/1.45      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 1.28/1.45         ((r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X5))
% 1.28/1.45          | ~ (r2_hidden @ X3 @ X5)
% 1.28/1.45          | ~ (r2_hidden @ X1 @ X2))),
% 1.28/1.45      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.28/1.45  thf('6', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.28/1.45         (((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.28/1.45          | ~ (r2_hidden @ X3 @ X2)
% 1.28/1.45          | (r2_hidden @ 
% 1.28/1.45             (k4_tarski @ X3 @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))) @ 
% 1.28/1.45             (k2_zfmisc_1 @ X2 @ X0)))),
% 1.28/1.45      inference('sup-', [status(thm)], ['4', '5'])).
% 1.28/1.45  thf('7', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.45         (((X0) = (k1_xboole_0))
% 1.28/1.45          | (r2_hidden @ 
% 1.28/1.45             (k4_tarski @ (sk_B @ X0) @ (sk_C_1 @ X1 @ (k2_zfmisc_1 @ X2 @ X1))) @ 
% 1.28/1.45             (k2_zfmisc_1 @ X0 @ X1))
% 1.28/1.45          | ((X1) = (k2_relat_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.28/1.45      inference('sup-', [status(thm)], ['0', '6'])).
% 1.28/1.45  thf('8', plain,
% 1.28/1.45      (![X20 : $i, X23 : $i, X24 : $i]:
% 1.28/1.45         (((X23) = (k2_relat_1 @ X20))
% 1.28/1.45          | ~ (r2_hidden @ (k4_tarski @ X24 @ (sk_C_1 @ X23 @ X20)) @ X20)
% 1.28/1.45          | ~ (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 1.28/1.45      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.28/1.45  thf('9', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         (((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.28/1.45          | ((X1) = (k1_xboole_0))
% 1.28/1.45          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 1.28/1.45          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.28/1.45      inference('sup-', [status(thm)], ['7', '8'])).
% 1.28/1.45  thf('10', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 1.28/1.45          | ((X1) = (k1_xboole_0))
% 1.28/1.45          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.28/1.45      inference('simplify', [status(thm)], ['9'])).
% 1.28/1.45  thf('11', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         ((r2_hidden @ (sk_C_1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)
% 1.28/1.45          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.28/1.45      inference('eq_fact', [status(thm)], ['3'])).
% 1.28/1.45  thf('12', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         (((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.28/1.45          | ((X1) = (k1_xboole_0)))),
% 1.28/1.45      inference('clc', [status(thm)], ['10', '11'])).
% 1.28/1.45  thf(t195_relat_1, conjecture,
% 1.28/1.45    (![A:$i,B:$i]:
% 1.28/1.45     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.28/1.45          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 1.28/1.45               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 1.28/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.45    (~( ![A:$i,B:$i]:
% 1.28/1.45        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.28/1.45             ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 1.28/1.45                  ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ) )),
% 1.28/1.45    inference('cnf.neg', [status(esa)], [t195_relat_1])).
% 1.28/1.45  thf('13', plain,
% 1.28/1.45      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) != (sk_A))
% 1.28/1.45        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) != (sk_B_1)))),
% 1.28/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.45  thf('14', plain,
% 1.28/1.45      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) != (sk_B_1)))
% 1.28/1.45         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_B_1))))),
% 1.28/1.45      inference('split', [status(esa)], ['13'])).
% 1.28/1.45  thf(d4_relat_1, axiom,
% 1.28/1.45    (![A:$i,B:$i]:
% 1.28/1.45     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.28/1.45       ( ![C:$i]:
% 1.28/1.45         ( ( r2_hidden @ C @ B ) <=>
% 1.28/1.45           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.28/1.45  thf('15', plain,
% 1.28/1.45      (![X13 : $i, X16 : $i]:
% 1.28/1.45         (((X16) = (k1_relat_1 @ X13))
% 1.28/1.45          | (r2_hidden @ 
% 1.28/1.45             (k4_tarski @ (sk_C @ X16 @ X13) @ (sk_D @ X16 @ X13)) @ X13)
% 1.28/1.45          | (r2_hidden @ (sk_C @ X16 @ X13) @ X16))),
% 1.28/1.45      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.28/1.45  thf('16', plain,
% 1.28/1.45      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.28/1.45         ((r2_hidden @ X1 @ X2)
% 1.28/1.45          | ~ (r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X4)))),
% 1.28/1.45      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.28/1.45  thf('17', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.45         ((r2_hidden @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2)
% 1.28/1.45          | ((X2) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.28/1.45          | (r2_hidden @ (sk_C @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) @ X1))),
% 1.28/1.45      inference('sup-', [status(thm)], ['15', '16'])).
% 1.28/1.45  thf('18', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         ((r2_hidden @ (sk_C @ X0 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)
% 1.28/1.45          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 1.28/1.45      inference('eq_fact', [status(thm)], ['17'])).
% 1.28/1.45  thf('19', plain,
% 1.28/1.45      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.28/1.45      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.28/1.45  thf('20', plain,
% 1.28/1.45      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 1.28/1.45         ((r2_hidden @ (k4_tarski @ X1 @ X3) @ (k2_zfmisc_1 @ X2 @ X5))
% 1.28/1.45          | ~ (r2_hidden @ X3 @ X5)
% 1.28/1.45          | ~ (r2_hidden @ X1 @ X2))),
% 1.28/1.45      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.28/1.45  thf('21', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.45         (((X0) = (k1_xboole_0))
% 1.28/1.45          | ~ (r2_hidden @ X2 @ X1)
% 1.28/1.45          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 1.28/1.45             (k2_zfmisc_1 @ X1 @ X0)))),
% 1.28/1.45      inference('sup-', [status(thm)], ['19', '20'])).
% 1.28/1.45  thf('22', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.45         (((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 1.28/1.45          | (r2_hidden @ 
% 1.28/1.45             (k4_tarski @ (sk_C @ X0 @ (k2_zfmisc_1 @ X0 @ X1)) @ (sk_B @ X2)) @ 
% 1.28/1.45             (k2_zfmisc_1 @ X0 @ X2))
% 1.28/1.45          | ((X2) = (k1_xboole_0)))),
% 1.28/1.45      inference('sup-', [status(thm)], ['18', '21'])).
% 1.28/1.45  thf('23', plain,
% 1.28/1.45      (![X13 : $i, X16 : $i, X17 : $i]:
% 1.28/1.45         (((X16) = (k1_relat_1 @ X13))
% 1.28/1.45          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X16 @ X13) @ X17) @ X13)
% 1.28/1.45          | ~ (r2_hidden @ (sk_C @ X16 @ X13) @ X16))),
% 1.28/1.45      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.28/1.45  thf('24', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         (((X0) = (k1_xboole_0))
% 1.28/1.45          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.28/1.45          | ~ (r2_hidden @ (sk_C @ X1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X1)
% 1.28/1.45          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.28/1.45      inference('sup-', [status(thm)], ['22', '23'])).
% 1.28/1.45  thf('25', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         (~ (r2_hidden @ (sk_C @ X1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X1)
% 1.28/1.45          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 1.28/1.45          | ((X0) = (k1_xboole_0)))),
% 1.28/1.45      inference('simplify', [status(thm)], ['24'])).
% 1.28/1.45  thf('26', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         ((r2_hidden @ (sk_C @ X0 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)
% 1.28/1.45          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 1.28/1.45      inference('eq_fact', [status(thm)], ['17'])).
% 1.28/1.45  thf('27', plain,
% 1.28/1.45      (![X0 : $i, X1 : $i]:
% 1.28/1.45         (((X0) = (k1_xboole_0))
% 1.28/1.45          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 1.28/1.45      inference('clc', [status(thm)], ['25', '26'])).
% 1.28/1.45  thf('28', plain,
% 1.28/1.45      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) != (sk_A)))
% 1.28/1.45         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_A))))),
% 1.28/1.45      inference('split', [status(esa)], ['13'])).
% 1.28/1.45  thf('29', plain,
% 1.28/1.45      (((((sk_A) != (sk_A)) | ((sk_B_1) = (k1_xboole_0))))
% 1.28/1.45         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_A))))),
% 1.28/1.45      inference('sup-', [status(thm)], ['27', '28'])).
% 1.28/1.45  thf('30', plain,
% 1.28/1.45      ((((sk_B_1) = (k1_xboole_0)))
% 1.28/1.45         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_A))))),
% 1.28/1.45      inference('simplify', [status(thm)], ['29'])).
% 1.28/1.45  thf('31', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.28/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.45  thf('32', plain, ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_A)))),
% 1.28/1.45      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 1.28/1.45  thf('33', plain,
% 1.28/1.45      (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_B_1))) | 
% 1.28/1.45       ~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_A)))),
% 1.28/1.45      inference('split', [status(esa)], ['13'])).
% 1.28/1.45  thf('34', plain,
% 1.28/1.45      (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_B_1)))),
% 1.28/1.45      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 1.28/1.45  thf('35', plain,
% 1.28/1.45      (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) != (sk_B_1))),
% 1.28/1.45      inference('simpl_trail', [status(thm)], ['14', '34'])).
% 1.28/1.45  thf('36', plain, ((((sk_B_1) != (sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 1.28/1.45      inference('sup-', [status(thm)], ['12', '35'])).
% 1.28/1.45  thf('37', plain, (((sk_A) = (k1_xboole_0))),
% 1.28/1.45      inference('simplify', [status(thm)], ['36'])).
% 1.28/1.45  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 1.28/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.45  thf('39', plain, ($false),
% 1.28/1.45      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 1.28/1.45  
% 1.28/1.45  % SZS output end Refutation
% 1.28/1.45  
% 1.28/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
