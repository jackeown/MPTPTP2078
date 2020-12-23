%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0898+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6Ne3AabVMY

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  66 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   12
%              Number of atoms          :  295 ( 954 expanded)
%              Number of equality atoms :   66 ( 195 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_zfmisc_1 @ A @ B @ C @ D )
        = ( k4_zfmisc_1 @ E @ F @ G @ H ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( C = k1_xboole_0 )
        | ( D = k1_xboole_0 )
        | ( ( A = E )
          & ( B = F )
          & ( C = G )
          & ( D = H ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 ) )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('2',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 ) )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t56_mcart_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( sk_B = X3 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_B = X3 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
       != ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['5'])).

thf('7',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('10',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('11',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X0 = sk_B )
      | ( X1 = sk_B )
      | ( X2 = sk_B )
      | ( X3 = sk_B )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ X4 @ X5 @ X6 @ X7 ) )
      | ( X3 = X4 ) ) ),
    inference(demod,[status(thm)],['1','8','9','10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( X3 = sk_B )
      | ( X3 = sk_B )
      | ( X2 = sk_B )
      | ( X1 = sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = sk_B )
      | ( X1 = sk_B )
      | ( X2 = sk_B )
      | ( X3 = sk_B )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference(eq_res,[status(thm)],['14'])).

thf('16',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).


%------------------------------------------------------------------------------
