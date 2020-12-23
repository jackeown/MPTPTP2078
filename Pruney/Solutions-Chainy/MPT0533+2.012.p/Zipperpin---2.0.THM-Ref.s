%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i9BWClS6aJ

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:45 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   63 (  77 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  467 ( 678 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(t133_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t133_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B_1 @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X24 )
      | ( ( k8_relat_1 @ X23 @ ( k8_relat_1 @ X22 @ X24 ) )
        = ( k8_relat_1 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X20 @ X21 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ X17 )
      | ( r2_hidden @ ( sk_B @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k4_tarski @ ( sk_C @ X15 ) @ ( sk_D_1 @ X15 ) ) )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k4_tarski @ ( sk_C @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) ) @ ( sk_D_1 @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ( ( sk_B @ X17 )
       != ( k4_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X20 @ X21 ) @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t132_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k8_relat_1 @ X26 @ X27 ) @ ( k8_relat_1 @ X26 @ X25 ) )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r1_tarski @ sk_C_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k8_relat_1 @ X26 @ X27 ) @ ( k8_relat_1 @ X26 @ X25 ) )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ ( k8_relat_1 @ X0 @ sk_D_2 ) )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ ( k8_relat_1 @ X0 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ ( k8_relat_1 @ X0 @ sk_D_2 ) )
      = ( k8_relat_1 @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D_2 ) @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.i9BWClS6aJ
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:48:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.28/1.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.28/1.49  % Solved by: fo/fo7.sh
% 1.28/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.49  % done 1659 iterations in 1.018s
% 1.28/1.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.28/1.49  % SZS output start Refutation
% 1.28/1.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.28/1.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.28/1.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.28/1.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.28/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.28/1.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.28/1.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.28/1.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.28/1.49  thf(sk_C_type, type, sk_C: $i > $i).
% 1.28/1.49  thf(sk_D_1_type, type, sk_D_1: $i > $i).
% 1.28/1.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.28/1.49  thf(sk_B_type, type, sk_B: $i > $i).
% 1.28/1.49  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.28/1.49  thf(t133_relat_1, conjecture,
% 1.28/1.49    (![A:$i,B:$i,C:$i]:
% 1.28/1.49     ( ( v1_relat_1 @ C ) =>
% 1.28/1.49       ( ![D:$i]:
% 1.28/1.49         ( ( v1_relat_1 @ D ) =>
% 1.28/1.49           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 1.28/1.49             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 1.28/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.49    (~( ![A:$i,B:$i,C:$i]:
% 1.28/1.49        ( ( v1_relat_1 @ C ) =>
% 1.28/1.49          ( ![D:$i]:
% 1.28/1.49            ( ( v1_relat_1 @ D ) =>
% 1.28/1.49              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 1.28/1.49                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 1.28/1.49    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 1.28/1.49  thf('0', plain,
% 1.28/1.49      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 1.28/1.49          (k8_relat_1 @ sk_B_1 @ sk_D_2))),
% 1.28/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.49  thf('1', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 1.28/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.49  thf(t129_relat_1, axiom,
% 1.28/1.49    (![A:$i,B:$i,C:$i]:
% 1.28/1.49     ( ( v1_relat_1 @ C ) =>
% 1.28/1.49       ( ( r1_tarski @ A @ B ) =>
% 1.28/1.49         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 1.28/1.49  thf('2', plain,
% 1.28/1.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.28/1.49         (~ (r1_tarski @ X22 @ X23)
% 1.28/1.49          | ~ (v1_relat_1 @ X24)
% 1.28/1.49          | ((k8_relat_1 @ X23 @ (k8_relat_1 @ X22 @ X24))
% 1.28/1.49              = (k8_relat_1 @ X22 @ X24)))),
% 1.28/1.49      inference('cnf', [status(esa)], [t129_relat_1])).
% 1.28/1.49  thf('3', plain,
% 1.28/1.49      (![X0 : $i]:
% 1.28/1.49         (((k8_relat_1 @ sk_B_1 @ (k8_relat_1 @ sk_A @ X0))
% 1.28/1.49            = (k8_relat_1 @ sk_A @ X0))
% 1.28/1.49          | ~ (v1_relat_1 @ X0))),
% 1.28/1.49      inference('sup-', [status(thm)], ['1', '2'])).
% 1.28/1.49  thf(t117_relat_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 1.28/1.49  thf('4', plain,
% 1.28/1.49      (![X20 : $i, X21 : $i]:
% 1.28/1.49         ((r1_tarski @ (k8_relat_1 @ X20 @ X21) @ X21) | ~ (v1_relat_1 @ X21))),
% 1.28/1.49      inference('cnf', [status(esa)], [t117_relat_1])).
% 1.28/1.49  thf(t28_xboole_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.28/1.49  thf('5', plain,
% 1.28/1.49      (![X11 : $i, X12 : $i]:
% 1.28/1.49         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 1.28/1.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.28/1.49  thf('6', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ X0)
% 1.28/1.49          | ((k3_xboole_0 @ (k8_relat_1 @ X1 @ X0) @ X0)
% 1.28/1.49              = (k8_relat_1 @ X1 @ X0)))),
% 1.28/1.49      inference('sup-', [status(thm)], ['4', '5'])).
% 1.28/1.49  thf(d1_relat_1, axiom,
% 1.28/1.49    (![A:$i]:
% 1.28/1.49     ( ( v1_relat_1 @ A ) <=>
% 1.28/1.49       ( ![B:$i]:
% 1.28/1.49         ( ~( ( r2_hidden @ B @ A ) & 
% 1.28/1.49              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 1.28/1.49  thf('7', plain,
% 1.28/1.49      (![X17 : $i]: ((v1_relat_1 @ X17) | (r2_hidden @ (sk_B @ X17) @ X17))),
% 1.28/1.49      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.28/1.49  thf(d4_xboole_0, axiom,
% 1.28/1.49    (![A:$i,B:$i,C:$i]:
% 1.28/1.49     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.28/1.49       ( ![D:$i]:
% 1.28/1.49         ( ( r2_hidden @ D @ C ) <=>
% 1.28/1.49           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.28/1.49  thf('8', plain,
% 1.28/1.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.28/1.49         (~ (r2_hidden @ X4 @ X3)
% 1.28/1.49          | (r2_hidden @ X4 @ X2)
% 1.28/1.49          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.28/1.49      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.28/1.49  thf('9', plain,
% 1.28/1.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.28/1.49         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.28/1.49      inference('simplify', [status(thm)], ['8'])).
% 1.28/1.49  thf('10', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.28/1.49          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.28/1.49      inference('sup-', [status(thm)], ['7', '9'])).
% 1.28/1.49  thf('11', plain,
% 1.28/1.49      (![X15 : $i, X16 : $i]:
% 1.28/1.49         (((X15) = (k4_tarski @ (sk_C @ X15) @ (sk_D_1 @ X15)))
% 1.28/1.49          | ~ (r2_hidden @ X15 @ X16)
% 1.28/1.49          | ~ (v1_relat_1 @ X16))),
% 1.28/1.49      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.28/1.49  thf('12', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.28/1.49          | ~ (v1_relat_1 @ X0)
% 1.28/1.49          | ((sk_B @ (k3_xboole_0 @ X1 @ X0))
% 1.28/1.49              = (k4_tarski @ (sk_C @ (sk_B @ (k3_xboole_0 @ X1 @ X0))) @ 
% 1.28/1.49                 (sk_D_1 @ (sk_B @ (k3_xboole_0 @ X1 @ X0))))))),
% 1.28/1.49      inference('sup-', [status(thm)], ['10', '11'])).
% 1.28/1.49  thf('13', plain,
% 1.28/1.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.28/1.49         ((v1_relat_1 @ X17) | ((sk_B @ X17) != (k4_tarski @ X18 @ X19)))),
% 1.28/1.49      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.28/1.49  thf('14', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.28/1.49      inference('clc', [status(thm)], ['12', '13'])).
% 1.28/1.49  thf('15', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.28/1.49          | ~ (v1_relat_1 @ X0)
% 1.28/1.49          | ~ (v1_relat_1 @ X0))),
% 1.28/1.49      inference('sup+', [status(thm)], ['6', '14'])).
% 1.28/1.49  thf('16', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 1.28/1.49      inference('simplify', [status(thm)], ['15'])).
% 1.28/1.49  thf('17', plain,
% 1.28/1.49      (![X20 : $i, X21 : $i]:
% 1.28/1.49         ((r1_tarski @ (k8_relat_1 @ X20 @ X21) @ X21) | ~ (v1_relat_1 @ X21))),
% 1.28/1.49      inference('cnf', [status(esa)], [t117_relat_1])).
% 1.28/1.49  thf(t132_relat_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( v1_relat_1 @ B ) =>
% 1.28/1.49       ( ![C:$i]:
% 1.28/1.49         ( ( v1_relat_1 @ C ) =>
% 1.28/1.49           ( ( r1_tarski @ B @ C ) =>
% 1.28/1.49             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 1.28/1.49  thf('18', plain,
% 1.28/1.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ X25)
% 1.28/1.49          | (r1_tarski @ (k8_relat_1 @ X26 @ X27) @ (k8_relat_1 @ X26 @ X25))
% 1.28/1.49          | ~ (r1_tarski @ X27 @ X25)
% 1.28/1.49          | ~ (v1_relat_1 @ X27))),
% 1.28/1.49      inference('cnf', [status(esa)], [t132_relat_1])).
% 1.28/1.49  thf('19', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ X0)
% 1.28/1.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.28/1.49          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.28/1.49             (k8_relat_1 @ X2 @ X0))
% 1.28/1.49          | ~ (v1_relat_1 @ X0))),
% 1.28/1.49      inference('sup-', [status(thm)], ['17', '18'])).
% 1.28/1.49  thf('20', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.49         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.28/1.49           (k8_relat_1 @ X2 @ X0))
% 1.28/1.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 1.28/1.49          | ~ (v1_relat_1 @ X0))),
% 1.28/1.49      inference('simplify', [status(thm)], ['19'])).
% 1.28/1.49  thf('21', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ X0)
% 1.28/1.49          | ~ (v1_relat_1 @ X0)
% 1.28/1.49          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.28/1.49             (k8_relat_1 @ X2 @ X0)))),
% 1.28/1.49      inference('sup-', [status(thm)], ['16', '20'])).
% 1.28/1.49  thf('22', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.49         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 1.28/1.49           (k8_relat_1 @ X2 @ X0))
% 1.28/1.49          | ~ (v1_relat_1 @ X0))),
% 1.28/1.49      inference('simplify', [status(thm)], ['21'])).
% 1.28/1.49  thf('23', plain,
% 1.28/1.49      (![X0 : $i]:
% 1.28/1.49         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B_1 @ X0))
% 1.28/1.49          | ~ (v1_relat_1 @ X0)
% 1.28/1.49          | ~ (v1_relat_1 @ X0))),
% 1.28/1.49      inference('sup+', [status(thm)], ['3', '22'])).
% 1.28/1.49  thf('24', plain,
% 1.28/1.49      (![X0 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ X0)
% 1.28/1.49          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B_1 @ X0)))),
% 1.28/1.49      inference('simplify', [status(thm)], ['23'])).
% 1.28/1.49  thf('25', plain, ((r1_tarski @ sk_C_1 @ sk_D_2)),
% 1.28/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.49  thf('26', plain,
% 1.28/1.49      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ X25)
% 1.28/1.49          | (r1_tarski @ (k8_relat_1 @ X26 @ X27) @ (k8_relat_1 @ X26 @ X25))
% 1.28/1.49          | ~ (r1_tarski @ X27 @ X25)
% 1.28/1.49          | ~ (v1_relat_1 @ X27))),
% 1.28/1.49      inference('cnf', [status(esa)], [t132_relat_1])).
% 1.28/1.49  thf('27', plain,
% 1.28/1.49      (![X0 : $i]:
% 1.28/1.49         (~ (v1_relat_1 @ sk_C_1)
% 1.28/1.49          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ 
% 1.28/1.49             (k8_relat_1 @ X0 @ sk_D_2))
% 1.28/1.49          | ~ (v1_relat_1 @ sk_D_2))),
% 1.28/1.49      inference('sup-', [status(thm)], ['25', '26'])).
% 1.28/1.49  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 1.28/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.49  thf('29', plain, ((v1_relat_1 @ sk_D_2)),
% 1.28/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.49  thf('30', plain,
% 1.28/1.49      (![X0 : $i]:
% 1.28/1.49         (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ (k8_relat_1 @ X0 @ sk_D_2))),
% 1.28/1.49      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.28/1.49  thf(t12_xboole_1, axiom,
% 1.28/1.49    (![A:$i,B:$i]:
% 1.28/1.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.28/1.49  thf('31', plain,
% 1.28/1.49      (![X9 : $i, X10 : $i]:
% 1.28/1.49         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 1.28/1.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.28/1.49  thf('32', plain,
% 1.28/1.49      (![X0 : $i]:
% 1.28/1.49         ((k2_xboole_0 @ (k8_relat_1 @ X0 @ sk_C_1) @ 
% 1.28/1.49           (k8_relat_1 @ X0 @ sk_D_2)) = (k8_relat_1 @ X0 @ sk_D_2))),
% 1.28/1.49      inference('sup-', [status(thm)], ['30', '31'])).
% 1.28/1.49  thf(t11_xboole_1, axiom,
% 1.28/1.49    (![A:$i,B:$i,C:$i]:
% 1.28/1.49     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.28/1.49  thf('33', plain,
% 1.28/1.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.28/1.49         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 1.28/1.49      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.28/1.49  thf('34', plain,
% 1.28/1.49      (![X0 : $i, X1 : $i]:
% 1.28/1.49         (~ (r1_tarski @ (k8_relat_1 @ X0 @ sk_D_2) @ X1)
% 1.28/1.49          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1))),
% 1.28/1.49      inference('sup-', [status(thm)], ['32', '33'])).
% 1.28/1.49  thf('35', plain,
% 1.28/1.49      ((~ (v1_relat_1 @ sk_D_2)
% 1.28/1.49        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 1.28/1.49           (k8_relat_1 @ sk_B_1 @ sk_D_2)))),
% 1.28/1.49      inference('sup-', [status(thm)], ['24', '34'])).
% 1.28/1.49  thf('36', plain, ((v1_relat_1 @ sk_D_2)),
% 1.28/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.49  thf('37', plain,
% 1.28/1.49      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 1.28/1.49        (k8_relat_1 @ sk_B_1 @ sk_D_2))),
% 1.28/1.49      inference('demod', [status(thm)], ['35', '36'])).
% 1.28/1.49  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 1.28/1.49  
% 1.28/1.49  % SZS output end Refutation
% 1.28/1.49  
% 1.33/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
