%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BB96hGy3Jz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:45 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   19 (  31 expanded)
%              Depth                    :   17
%              Number of atoms          :  417 ( 657 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_3 ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k8_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ X10 @ ( k6_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k8_relat_1 @ X11 @ X10 )
        = ( k5_relat_1 @ X10 @ ( k6_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_C_3 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ( ( r2_hidden @ C @ A )
           => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) )
       => ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X16 @ X17 ) @ X17 )
      | ( r1_tarski @ ( k6_relat_1 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(d10_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
          <=> ( ( r2_hidden @ C @ A )
              & ( C = D ) ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ( X4
       != ( k6_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X4 )
      | ( X6 != X8 )
      | ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_relat_1])).

thf('10',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X8 ) @ ( k6_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X8 ) @ ( k6_relat_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ sk_A ) @ ( sk_C_2 @ X0 @ sk_A ) ) @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X16 @ X17 ) @ ( sk_C_2 @ X16 @ X17 ) ) @ X16 )
      | ( r1_tarski @ ( k6_relat_1 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('18',plain,
    ( ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t50_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( v1_relat_1 @ D )
                 => ( ( ( r1_tarski @ A @ B )
                      & ( r1_tarski @ C @ D ) )
                   => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k5_relat_1 @ X14 @ X15 ) @ ( k5_relat_1 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_A ) ) @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ sk_A ) ) @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k5_relat_1 @ sk_C_3 @ ( k6_relat_1 @ sk_A ) ) @ ( k5_relat_1 @ sk_D_1 @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['3','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ ( k5_relat_1 @ sk_C_3 @ ( k6_relat_1 @ sk_A ) ) @ ( k5_relat_1 @ sk_D_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_3 ) @ ( k5_relat_1 @ sk_D_1 @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['2','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_3 ) @ ( k5_relat_1 @ sk_D_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_3 ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['1','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_3 ) @ ( k8_relat_1 @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BB96hGy3Jz
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:21:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 198 iterations in 0.242s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.53/0.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.53/0.71  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.53/0.71  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.53/0.71  thf(t133_relat_1, conjecture,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ C ) =>
% 0.53/0.71       ( ![D:$i]:
% 0.53/0.71         ( ( v1_relat_1 @ D ) =>
% 0.53/0.71           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.53/0.71             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.71        ( ( v1_relat_1 @ C ) =>
% 0.53/0.71          ( ![D:$i]:
% 0.53/0.71            ( ( v1_relat_1 @ D ) =>
% 0.53/0.71              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.53/0.71                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_3) @ 
% 0.53/0.71          (k8_relat_1 @ sk_B @ sk_D_1))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t123_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      (![X10 : $i, X11 : $i]:
% 0.53/0.71         (((k8_relat_1 @ X11 @ X10) = (k5_relat_1 @ X10 @ (k6_relat_1 @ X11)))
% 0.53/0.71          | ~ (v1_relat_1 @ X10))),
% 0.53/0.71      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      (![X10 : $i, X11 : $i]:
% 0.53/0.71         (((k8_relat_1 @ X11 @ X10) = (k5_relat_1 @ X10 @ (k6_relat_1 @ X11)))
% 0.53/0.71          | ~ (v1_relat_1 @ X10))),
% 0.53/0.71      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.53/0.71  thf('3', plain, ((r1_tarski @ sk_C_3 @ sk_D_1)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t73_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( ( ![C:$i]:
% 0.53/0.71           ( ( r2_hidden @ C @ A ) => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) ) ) =>
% 0.53/0.71         ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.53/0.71  thf('4', plain,
% 0.53/0.71      (![X16 : $i, X17 : $i]:
% 0.53/0.71         ((r2_hidden @ (sk_C_2 @ X16 @ X17) @ X17)
% 0.53/0.71          | (r1_tarski @ (k6_relat_1 @ X17) @ X16)
% 0.53/0.71          | ~ (v1_relat_1 @ X16))),
% 0.53/0.71      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.53/0.71  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(d3_tarski, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.53/0.71          | (r2_hidden @ X0 @ X2)
% 0.53/0.71          | ~ (r1_tarski @ X1 @ X2))),
% 0.53/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.71  thf('7', plain,
% 0.53/0.71      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.71  thf('8', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X0)
% 0.53/0.71          | (r1_tarski @ (k6_relat_1 @ sk_A) @ X0)
% 0.53/0.71          | (r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ sk_B))),
% 0.53/0.71      inference('sup-', [status(thm)], ['4', '7'])).
% 0.53/0.71  thf(d10_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.53/0.71         ( ![C:$i,D:$i]:
% 0.53/0.71           ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.53/0.71             ( ( r2_hidden @ C @ A ) & ( ( C ) = ( D ) ) ) ) ) ) ))).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X4 : $i, X5 : $i, X6 : $i, X8 : $i]:
% 0.53/0.71         (((X4) != (k6_relat_1 @ X5))
% 0.53/0.71          | (r2_hidden @ (k4_tarski @ X6 @ X8) @ X4)
% 0.53/0.71          | ((X6) != (X8))
% 0.53/0.71          | ~ (r2_hidden @ X6 @ X5)
% 0.53/0.71          | ~ (v1_relat_1 @ X4))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_relat_1])).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      (![X5 : $i, X8 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ (k6_relat_1 @ X5))
% 0.53/0.71          | ~ (r2_hidden @ X8 @ X5)
% 0.53/0.71          | (r2_hidden @ (k4_tarski @ X8 @ X8) @ (k6_relat_1 @ X5)))),
% 0.53/0.71      inference('simplify', [status(thm)], ['9'])).
% 0.53/0.71  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.53/0.71  thf('11', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      (![X5 : $i, X8 : $i]:
% 0.53/0.71         (~ (r2_hidden @ X8 @ X5)
% 0.53/0.71          | (r2_hidden @ (k4_tarski @ X8 @ X8) @ (k6_relat_1 @ X5)))),
% 0.53/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.53/0.71  thf('13', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((r1_tarski @ (k6_relat_1 @ sk_A) @ X0)
% 0.53/0.71          | ~ (v1_relat_1 @ X0)
% 0.53/0.71          | (r2_hidden @ 
% 0.53/0.71             (k4_tarski @ (sk_C_2 @ X0 @ sk_A) @ (sk_C_2 @ X0 @ sk_A)) @ 
% 0.53/0.71             (k6_relat_1 @ sk_B)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['8', '12'])).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      (![X16 : $i, X17 : $i]:
% 0.53/0.71         (~ (r2_hidden @ 
% 0.53/0.71             (k4_tarski @ (sk_C_2 @ X16 @ X17) @ (sk_C_2 @ X16 @ X17)) @ X16)
% 0.53/0.71          | (r1_tarski @ (k6_relat_1 @ X17) @ X16)
% 0.53/0.71          | ~ (v1_relat_1 @ X16))),
% 0.53/0.71      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.53/0.71  thf('15', plain,
% 0.53/0.71      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.53/0.71        | (r1_tarski @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_B))
% 0.53/0.71        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.53/0.71        | (r1_tarski @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_B)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['13', '14'])).
% 0.53/0.71  thf('16', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.71  thf('17', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.71  thf('18', plain,
% 0.53/0.71      (((r1_tarski @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_B))
% 0.53/0.71        | (r1_tarski @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.53/0.71  thf('19', plain, ((r1_tarski @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ sk_B))),
% 0.53/0.71      inference('simplify', [status(thm)], ['18'])).
% 0.53/0.71  thf(t50_relat_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ A ) =>
% 0.53/0.71       ( ![B:$i]:
% 0.53/0.71         ( ( v1_relat_1 @ B ) =>
% 0.53/0.71           ( ![C:$i]:
% 0.53/0.71             ( ( v1_relat_1 @ C ) =>
% 0.53/0.71               ( ![D:$i]:
% 0.53/0.71                 ( ( v1_relat_1 @ D ) =>
% 0.53/0.71                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.53/0.71                     ( r1_tarski @
% 0.53/0.71                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X12)
% 0.53/0.71          | ~ (v1_relat_1 @ X13)
% 0.53/0.71          | (r1_tarski @ (k5_relat_1 @ X14 @ X15) @ (k5_relat_1 @ X12 @ X13))
% 0.53/0.71          | ~ (r1_tarski @ X15 @ X13)
% 0.53/0.71          | ~ (r1_tarski @ X14 @ X12)
% 0.53/0.71          | ~ (v1_relat_1 @ X15)
% 0.53/0.71          | ~ (v1_relat_1 @ X14))),
% 0.53/0.71      inference('cnf', [status(esa)], [t50_relat_1])).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X0)
% 0.53/0.71          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.53/0.71          | ~ (r1_tarski @ X0 @ X1)
% 0.53/0.71          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_A)) @ 
% 0.53/0.71             (k5_relat_1 @ X1 @ (k6_relat_1 @ sk_B)))
% 0.53/0.71          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.53/0.71          | ~ (v1_relat_1 @ X1))),
% 0.53/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.53/0.71  thf('22', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.71  thf('23', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.53/0.71  thf('24', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X0)
% 0.53/0.71          | ~ (r1_tarski @ X0 @ X1)
% 0.53/0.71          | (r1_tarski @ (k5_relat_1 @ X0 @ (k6_relat_1 @ sk_A)) @ 
% 0.53/0.71             (k5_relat_1 @ X1 @ (k6_relat_1 @ sk_B)))
% 0.53/0.71          | ~ (v1_relat_1 @ X1))),
% 0.53/0.71      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.53/0.71  thf('25', plain,
% 0.53/0.71      ((~ (v1_relat_1 @ sk_D_1)
% 0.53/0.71        | (r1_tarski @ (k5_relat_1 @ sk_C_3 @ (k6_relat_1 @ sk_A)) @ 
% 0.53/0.71           (k5_relat_1 @ sk_D_1 @ (k6_relat_1 @ sk_B)))
% 0.53/0.71        | ~ (v1_relat_1 @ sk_C_3))),
% 0.53/0.71      inference('sup-', [status(thm)], ['3', '24'])).
% 0.53/0.71  thf('26', plain, ((v1_relat_1 @ sk_D_1)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('27', plain, ((v1_relat_1 @ sk_C_3)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('28', plain,
% 0.53/0.71      ((r1_tarski @ (k5_relat_1 @ sk_C_3 @ (k6_relat_1 @ sk_A)) @ 
% 0.53/0.71        (k5_relat_1 @ sk_D_1 @ (k6_relat_1 @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_3) @ 
% 0.53/0.71         (k5_relat_1 @ sk_D_1 @ (k6_relat_1 @ sk_B)))
% 0.53/0.71        | ~ (v1_relat_1 @ sk_C_3))),
% 0.53/0.71      inference('sup+', [status(thm)], ['2', '28'])).
% 0.53/0.71  thf('30', plain, ((v1_relat_1 @ sk_C_3)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('31', plain,
% 0.53/0.71      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_3) @ 
% 0.53/0.71        (k5_relat_1 @ sk_D_1 @ (k6_relat_1 @ sk_B)))),
% 0.53/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.53/0.71  thf('32', plain,
% 0.53/0.71      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_3) @ 
% 0.53/0.71         (k8_relat_1 @ sk_B @ sk_D_1))
% 0.53/0.71        | ~ (v1_relat_1 @ sk_D_1))),
% 0.53/0.71      inference('sup+', [status(thm)], ['1', '31'])).
% 0.53/0.71  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('34', plain,
% 0.53/0.71      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_3) @ (k8_relat_1 @ sk_B @ sk_D_1))),
% 0.53/0.71      inference('demod', [status(thm)], ['32', '33'])).
% 0.53/0.71  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
