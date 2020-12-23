%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g08vDdzmKf

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  74 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :  490 ( 819 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

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

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t131_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k8_relat_1 @ X7 @ X9 ) @ ( k8_relat_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t131_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('6',plain,(
    r1_tarski @ sk_C_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k8_relat_1 @ X11 @ X12 ) @ ( k8_relat_1 @ X11 @ X10 ) )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ ( k8_relat_1 @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( sk_D @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) @ ( k8_relat_1 @ X0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( sk_D @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) @ ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( sk_D @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) @ ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( sk_D @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) @ X2 )
      | ~ ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D_1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D_1 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( sk_D @ X2 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D_1 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( sk_D @ X2 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) ) @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) @ ( sk_D @ X0 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_D @ X0 @ X1 ) ) @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('29',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g08vDdzmKf
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:38:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 99 iterations in 0.117s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.55  thf(dt_k8_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.55  thf(t133_relat_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ C ) =>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( v1_relat_1 @ D ) =>
% 0.21/0.55           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.21/0.55             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( v1_relat_1 @ C ) =>
% 0.21/0.55          ( ![D:$i]:
% 0.21/0.55            ( ( v1_relat_1 @ D ) =>
% 0.21/0.55              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.21/0.55                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 0.21/0.55  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t131_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ C ) =>
% 0.21/0.55       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.55         ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.55          | ~ (v1_relat_1 @ X9)
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ X7 @ X9) @ (k8_relat_1 @ X8 @ X9)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t131_relat_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i]:
% 0.21/0.55         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.55  thf('6', plain, ((r1_tarski @ sk_C_1 @ sk_D_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t132_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( v1_relat_1 @ C ) =>
% 0.21/0.55           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.55             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X10)
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ X11 @ X12) @ (k8_relat_1 @ X11 @ X10))
% 0.21/0.55          | ~ (r1_tarski @ X12 @ X10)
% 0.21/0.55          | ~ (v1_relat_1 @ X12))),
% 0.21/0.55      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ 
% 0.21/0.55             (k8_relat_1 @ X0 @ sk_D_1))
% 0.21/0.55          | ~ (v1_relat_1 @ sk_D_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('10', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ (k8_relat_1 @ X0 @ sk_D_1))),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.55  thf(d3_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55           ( ![C:$i,D:$i]:
% 0.21/0.55             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.55               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X1)
% 0.21/0.55          | (r1_tarski @ X1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X2)
% 0.21/0.55          | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ X2)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X2)
% 0.21/0.55          | (r1_tarski @ X0 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_C_1))
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.55              (sk_D @ X1 @ (k8_relat_1 @ X0 @ sk_C_1))) @ 
% 0.21/0.55             (k8_relat_1 @ X0 @ sk_D_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.55              (sk_D @ X1 @ (k8_relat_1 @ X0 @ sk_C_1))) @ 
% 0.21/0.55             (k8_relat_1 @ X0 @ sk_D_1))
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['5', '16'])).
% 0.21/0.55  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ 
% 0.21/0.55           (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.55            (sk_D @ X1 @ (k8_relat_1 @ X0 @ sk_C_1))) @ 
% 0.21/0.55           (k8_relat_1 @ X0 @ sk_D_1))
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.55          | (r2_hidden @ (k4_tarski @ X3 @ X4) @ X2)
% 0.21/0.55          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_D_1))
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.55              (sk_D @ X1 @ (k8_relat_1 @ X0 @ sk_C_1))) @ 
% 0.21/0.55             X2)
% 0.21/0.55          | ~ (r1_tarski @ (k8_relat_1 @ X0 @ sk_D_1) @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ sk_D_1)
% 0.21/0.55          | ~ (r1_tarski @ (k8_relat_1 @ X0 @ sk_D_1) @ X1)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.55              (sk_D @ X2 @ (k8_relat_1 @ X0 @ sk_C_1))) @ 
% 0.21/0.55             X1)
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '21'])).
% 0.21/0.55  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_tarski @ (k8_relat_1 @ X0 @ sk_D_1) @ X1)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X2 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.55              (sk_D @ X2 @ (k8_relat_1 @ X0 @ sk_C_1))) @ 
% 0.21/0.55             X1)
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X2))),
% 0.21/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ sk_D_1)
% 0.21/0.55          | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.21/0.55              (sk_D @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1))) @ 
% 0.21/0.55             (k8_relat_1 @ sk_B @ sk_D_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '24'])).
% 0.21/0.55  thf('26', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k4_tarski @ (sk_C @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1)) @ 
% 0.21/0.55              (sk_D @ X0 @ (k8_relat_1 @ sk_A @ sk_C_1))) @ 
% 0.21/0.55             (k8_relat_1 @ sk_B @ sk_D_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_D @ X0 @ X1)) @ X0)
% 0.21/0.55          | (r1_tarski @ X1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.55         (k8_relat_1 @ sk_B @ sk_D_1))
% 0.21/0.55        | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1))
% 0.21/0.55        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.55           (k8_relat_1 @ sk_B @ sk_D_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1))
% 0.21/0.55        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.55           (k8_relat_1 @ sk_B @ sk_D_1)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.55          (k8_relat_1 @ sk_B @ sk_D_1))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain, (~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ sk_C_1))),
% 0.21/0.55      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('33', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '32'])).
% 0.21/0.55  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('35', plain, ($false), inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
