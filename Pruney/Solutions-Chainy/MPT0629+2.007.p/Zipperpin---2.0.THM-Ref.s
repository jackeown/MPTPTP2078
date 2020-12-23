%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vFrFWhUXSM

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  287 ( 479 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t25_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
             => ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('4',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X4 @ X2 ) @ X4 ) @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_A ) @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( X9
       != ( k5_relat_1 @ X8 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X13 @ X10 @ X7 @ X8 ) @ X13 ) @ X7 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X13 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X13 ) @ ( k5_relat_1 @ X8 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X13 @ X10 @ X7 @ X8 ) @ X13 ) @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_A @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_A @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_A @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_F_1 @ sk_A @ ( sk_D_1 @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B ) ) @ sk_B @ sk_C_1 ) @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k2_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vFrFWhUXSM
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 39 iterations in 0.053s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(t25_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50           ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.21/0.50             ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50          ( ![C:$i]:
% 0.21/0.50            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50              ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.21/0.50                ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t25_funct_1])).
% 0.21/0.50  thf('0', plain, (~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k5_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.50       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X15)
% 0.21/0.50          | ~ (v1_relat_1 @ X16)
% 0.21/0.50          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((r2_hidden @ sk_A @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d5_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.50           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X4 @ X3)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.21/0.50          | ((X3) != (k2_relat_1 @ X2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X2 : $i, X4 : $i]:
% 0.21/0.50         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X4 @ X2) @ X4) @ X2)
% 0.21/0.50          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X2)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((r2_hidden @ 
% 0.21/0.50        (k4_tarski @ (sk_D_1 @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B)) @ sk_A) @ 
% 0.21/0.50        (k5_relat_1 @ sk_C_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.50  thf(d8_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ B ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( v1_relat_1 @ C ) =>
% 0.21/0.50               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.21/0.50                 ( ![D:$i,E:$i]:
% 0.21/0.50                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.21/0.50                     ( ?[F:$i]:
% 0.21/0.50                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.21/0.50                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X13 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X7)
% 0.21/0.50          | ((X9) != (k5_relat_1 @ X8 @ X7))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X13 @ X10 @ X7 @ X8) @ X13) @ 
% 0.21/0.50             X7)
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X10 @ X13) @ X9)
% 0.21/0.50          | ~ (v1_relat_1 @ X9)
% 0.21/0.50          | ~ (v1_relat_1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X10 : $i, X13 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X8)
% 0.21/0.50          | ~ (v1_relat_1 @ (k5_relat_1 @ X8 @ X7))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X10 @ X13) @ (k5_relat_1 @ X8 @ X7))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X13 @ X10 @ X7 @ X8) @ X13) @ 
% 0.21/0.50             X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | (r2_hidden @ 
% 0.21/0.50           (k4_tarski @ 
% 0.21/0.50            (sk_F_1 @ sk_A @ (sk_D_1 @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.21/0.50             sk_B @ sk_C_1) @ 
% 0.21/0.50            sk_A) @ 
% 0.21/0.50           sk_B)
% 0.21/0.50        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.50  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (((r2_hidden @ 
% 0.21/0.50         (k4_tarski @ 
% 0.21/0.50          (sk_F_1 @ sk_A @ (sk_D_1 @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.21/0.50           sk_B @ sk_C_1) @ 
% 0.21/0.50          sk_A) @ 
% 0.21/0.50         sk_B)
% 0.21/0.50        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.50        | (r2_hidden @ 
% 0.21/0.50           (k4_tarski @ 
% 0.21/0.50            (sk_F_1 @ sk_A @ (sk_D_1 @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.21/0.50             sk_B @ sk_C_1) @ 
% 0.21/0.50            sk_A) @ 
% 0.21/0.50           sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '11'])).
% 0.21/0.50  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((r2_hidden @ 
% 0.21/0.50        (k4_tarski @ 
% 0.21/0.50         (sk_F_1 @ sk_A @ (sk_D_1 @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.21/0.50          sk_B @ sk_C_1) @ 
% 0.21/0.50         sk_A) @ 
% 0.21/0.50        sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.21/0.50          | (r2_hidden @ X1 @ X3)
% 0.21/0.50          | ((X3) != (k2_relat_1 @ X2)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ (k2_relat_1 @ X2))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.50  thf('18', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.50  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
