%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.enE4JhBsfU

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  327 ( 558 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( ( k8_relat_1 @ X9 @ ( k8_relat_1 @ X8 @ X10 ) )
        = ( k8_relat_1 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X6 @ X7 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_tarski @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ sk_D )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C_1 ) @ sk_D ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t132_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k8_relat_1 @ X12 @ X13 ) @ ( k8_relat_1 @ X12 @ X11 ) )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( k8_relat_1 @ X1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( k8_relat_1 @ X1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( k8_relat_1 @ X1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C_1 ) ) @ ( k8_relat_1 @ X1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.enE4JhBsfU
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 65 iterations in 0.068s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(t133_relat_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ C ) =>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ D ) =>
% 0.21/0.52           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.21/0.52             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( v1_relat_1 @ C ) =>
% 0.21/0.52          ( ![D:$i]:
% 0.21/0.52            ( ( v1_relat_1 @ D ) =>
% 0.21/0.52              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.21/0.52                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t129_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ C ) =>
% 0.21/0.52       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X8 @ X9)
% 0.21/0.52          | ~ (v1_relat_1 @ X10)
% 0.21/0.52          | ((k8_relat_1 @ X9 @ (k8_relat_1 @ X8 @ X10))
% 0.21/0.52              = (k8_relat_1 @ X8 @ X10)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.53         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.21/0.53            = (k8_relat_1 @ sk_A @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(dt_k8_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         ((v1_relat_1 @ (k8_relat_1 @ X4 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf(t117_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((r1_tarski @ (k8_relat_1 @ X6 @ X7) @ X7) | ~ (v1_relat_1 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r2_hidden @ X2 @ X0)
% 0.21/0.53          | ~ (r2_hidden @ X2 @ (k8_relat_1 @ X1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X2 @ (k8_relat_1 @ X1 @ X0)) @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.53  thf('10', plain, ((r1_tarski @ sk_C_1 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ sk_C_1)
% 0.21/0.53          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.53  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ X1)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ sk_D)
% 0.21/0.53          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i]: (r1_tarski @ (k8_relat_1 @ X0 @ sk_C_1) @ sk_D)),
% 0.21/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.53  thf(t132_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ C ) =>
% 0.21/0.53           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.53             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X11)
% 0.21/0.53          | (r1_tarski @ (k8_relat_1 @ X12 @ X13) @ (k8_relat_1 @ X12 @ X11))
% 0.21/0.53          | ~ (r1_tarski @ X13 @ X11)
% 0.21/0.53          | ~ (v1_relat_1 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_C_1))
% 0.21/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.53             (k8_relat_1 @ X1 @ sk_D))
% 0.21/0.53          | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_C_1))
% 0.21/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.53             (k8_relat_1 @ X1 @ sk_D)))),
% 0.21/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ sk_C_1)
% 0.21/0.53          | (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.53             (k8_relat_1 @ X1 @ sk_D)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '22'])).
% 0.21/0.53  thf('24', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C_1)) @ 
% 0.21/0.53          (k8_relat_1 @ X1 @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ (k8_relat_1 @ sk_B @ sk_D))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['3', '25'])).
% 0.21/0.53  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
