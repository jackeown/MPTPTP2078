%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2KZtRijFNQ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:34 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  441 ( 666 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t158_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_A @ ( sk_C @ X1 @ ( k9_relat_1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X1 @ X0 @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_C @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_C_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C_1 @ X0 @ ( sk_C @ X1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) ) @ ( sk_C @ X1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C_1 @ X0 @ ( sk_C @ X1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) ) @ ( sk_C @ X1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) ) @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i,X11: $i] :
      ( ( X8
       != ( k9_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X10 ) @ X6 )
      | ~ ( r2_hidden @ X11 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X10 ) @ X6 )
      | ( r2_hidden @ X10 @ ( k9_relat_1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) @ ( k9_relat_1 @ sk_D_2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ X0 @ ( sk_C @ X1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) ) @ X2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) @ ( k9_relat_1 @ sk_D_2 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ sk_C_1 @ X0 @ ( sk_C @ X1 @ ( k9_relat_1 @ sk_C_1 @ X0 ) ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_2 @ sk_B ) )
    | ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_D_2 @ sk_B ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2KZtRijFNQ
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 96 iterations in 0.157s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.41/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(t158_relat_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ C ) =>
% 0.41/0.61       ( ![D:$i]:
% 0.41/0.61         ( ( v1_relat_1 @ D ) =>
% 0.41/0.61           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.41/0.61             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( v1_relat_1 @ C ) =>
% 0.41/0.61          ( ![D:$i]:
% 0.41/0.61            ( ( v1_relat_1 @ D ) =>
% 0.41/0.61              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.41/0.61                ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t158_relat_1])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      (~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.41/0.61          (k9_relat_1 @ sk_D_2 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d3_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf(t143_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ C ) =>
% 0.41/0.61       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.41/0.61         ( ?[D:$i]:
% 0.41/0.61           ( ( r2_hidden @ D @ B ) & 
% 0.41/0.61             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.41/0.61             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.41/0.61          | (r2_hidden @ (sk_D_1 @ X15 @ X13 @ X14) @ X13)
% 0.41/0.61          | ~ (v1_relat_1 @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.41/0.61          | ~ (v1_relat_1 @ X1)
% 0.41/0.61          | (r2_hidden @ 
% 0.41/0.61             (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.61  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ X0)
% 0.41/0.61          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ X1)
% 0.41/0.61          | (r2_hidden @ 
% 0.41/0.61             (sk_D_1 @ X0 @ sk_A @ (sk_C @ X1 @ (k9_relat_1 @ X0 @ sk_A))) @ 
% 0.41/0.61             sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '6'])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.41/0.61          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X15 @ X13 @ X14) @ X14) @ X15)
% 0.41/0.61          | ~ (v1_relat_1 @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.41/0.61          | ~ (v1_relat_1 @ X1)
% 0.41/0.61          | (r2_hidden @ 
% 0.41/0.61             (k4_tarski @ 
% 0.41/0.61              (sk_D_1 @ X1 @ X0 @ (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.41/0.61              (sk_C @ X2 @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.41/0.61             X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf('11', plain, ((r1_tarski @ sk_C_1 @ sk_D_2)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X0 : $i]: ((r2_hidden @ X0 @ sk_D_2) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ sk_C_1)
% 0.41/0.61          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ X1)
% 0.41/0.61          | (r2_hidden @ 
% 0.41/0.61             (k4_tarski @ 
% 0.41/0.61              (sk_D_1 @ sk_C_1 @ X0 @ (sk_C @ X1 @ (k9_relat_1 @ sk_C_1 @ X0))) @ 
% 0.41/0.61              (sk_C @ X1 @ (k9_relat_1 @ sk_C_1 @ X0))) @ 
% 0.41/0.61             sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['10', '13'])).
% 0.44/0.61  thf('15', plain, ((v1_relat_1 @ sk_C_1)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('16', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i]:
% 0.44/0.61         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ X1)
% 0.44/0.61          | (r2_hidden @ 
% 0.44/0.61             (k4_tarski @ 
% 0.44/0.61              (sk_D_1 @ sk_C_1 @ X0 @ (sk_C @ X1 @ (k9_relat_1 @ sk_C_1 @ X0))) @ 
% 0.44/0.61              (sk_C @ X1 @ (k9_relat_1 @ sk_C_1 @ X0))) @ 
% 0.44/0.61             sk_D_2))),
% 0.44/0.61      inference('demod', [status(thm)], ['14', '15'])).
% 0.44/0.61  thf(d13_relat_1, axiom,
% 0.44/0.61    (![A:$i]:
% 0.44/0.61     ( ( v1_relat_1 @ A ) =>
% 0.44/0.61       ( ![B:$i,C:$i]:
% 0.44/0.61         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.44/0.61           ( ![D:$i]:
% 0.44/0.61             ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.61               ( ?[E:$i]:
% 0.44/0.61                 ( ( r2_hidden @ E @ B ) & 
% 0.44/0.61                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.44/0.61  thf('17', plain,
% 0.44/0.61      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.44/0.61         (((X8) != (k9_relat_1 @ X6 @ X5))
% 0.44/0.61          | (r2_hidden @ X10 @ X8)
% 0.44/0.61          | ~ (r2_hidden @ (k4_tarski @ X11 @ X10) @ X6)
% 0.44/0.61          | ~ (r2_hidden @ X11 @ X5)
% 0.44/0.61          | ~ (v1_relat_1 @ X6))),
% 0.44/0.61      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.44/0.61  thf('18', plain,
% 0.44/0.61      (![X5 : $i, X6 : $i, X10 : $i, X11 : $i]:
% 0.44/0.61         (~ (v1_relat_1 @ X6)
% 0.44/0.61          | ~ (r2_hidden @ X11 @ X5)
% 0.44/0.61          | ~ (r2_hidden @ (k4_tarski @ X11 @ X10) @ X6)
% 0.44/0.61          | (r2_hidden @ X10 @ (k9_relat_1 @ X6 @ X5)))),
% 0.44/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.44/0.61  thf('19', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ X1)
% 0.44/0.61          | (r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ sk_C_1 @ X0)) @ 
% 0.44/0.61             (k9_relat_1 @ sk_D_2 @ X2))
% 0.44/0.61          | ~ (r2_hidden @ 
% 0.44/0.61               (sk_D_1 @ sk_C_1 @ X0 @ (sk_C @ X1 @ (k9_relat_1 @ sk_C_1 @ X0))) @ 
% 0.44/0.61               X2)
% 0.44/0.61          | ~ (v1_relat_1 @ sk_D_2))),
% 0.44/0.61      inference('sup-', [status(thm)], ['16', '18'])).
% 0.44/0.61  thf('20', plain, ((v1_relat_1 @ sk_D_2)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('21', plain,
% 0.44/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.61         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ X0) @ X1)
% 0.44/0.61          | (r2_hidden @ (sk_C @ X1 @ (k9_relat_1 @ sk_C_1 @ X0)) @ 
% 0.44/0.61             (k9_relat_1 @ sk_D_2 @ X2))
% 0.44/0.61          | ~ (r2_hidden @ 
% 0.44/0.61               (sk_D_1 @ sk_C_1 @ X0 @ (sk_C @ X1 @ (k9_relat_1 @ sk_C_1 @ X0))) @ 
% 0.44/0.61               X2))),
% 0.44/0.61      inference('demod', [status(thm)], ['19', '20'])).
% 0.44/0.61  thf('22', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.44/0.61          | ~ (v1_relat_1 @ sk_C_1)
% 0.44/0.61          | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.44/0.61             (k9_relat_1 @ sk_D_2 @ sk_B))
% 0.44/0.61          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.44/0.61      inference('sup-', [status(thm)], ['7', '21'])).
% 0.44/0.61  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.44/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.61  thf('24', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0)
% 0.44/0.61          | (r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.44/0.61             (k9_relat_1 @ sk_D_2 @ sk_B))
% 0.44/0.61          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.44/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.44/0.61  thf('25', plain,
% 0.44/0.61      (![X0 : $i]:
% 0.44/0.61         ((r2_hidden @ (sk_C @ X0 @ (k9_relat_1 @ sk_C_1 @ sk_A)) @ 
% 0.44/0.61           (k9_relat_1 @ sk_D_2 @ sk_B))
% 0.44/0.61          | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.44/0.61      inference('simplify', [status(thm)], ['24'])).
% 0.44/0.61  thf('26', plain,
% 0.44/0.61      (![X1 : $i, X3 : $i]:
% 0.44/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.61  thf('27', plain,
% 0.44/0.61      (((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.44/0.61         (k9_relat_1 @ sk_D_2 @ sk_B))
% 0.44/0.61        | (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.44/0.61           (k9_relat_1 @ sk_D_2 @ sk_B)))),
% 0.44/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.44/0.61  thf('28', plain,
% 0.44/0.61      ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ (k9_relat_1 @ sk_D_2 @ sk_B))),
% 0.44/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.44/0.61  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.44/0.61  
% 0.44/0.61  % SZS output end Refutation
% 0.44/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
