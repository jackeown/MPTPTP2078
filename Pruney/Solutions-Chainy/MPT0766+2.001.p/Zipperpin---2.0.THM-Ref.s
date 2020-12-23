%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fw6regVVk3

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  70 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  238 (1255 expanded)
%              Number of equality atoms :    2 (  24 expanded)
%              Maximal formula depth    :   23 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t12_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ? [C: $i] :
                  ( ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A )
                  & ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                    & ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
                    & ! [D: $i] :
                        ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                          & ( r2_hidden @ ( k4_tarski @ B @ D ) @ A )
                          & ( D != B )
                          & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v2_wellord1 @ A )
         => ! [B: $i] :
              ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
                & ? [C: $i] :
                    ( ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A )
                    & ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) )
                & ! [C: $i] :
                    ~ ( ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
                      & ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
                      & ! [D: $i] :
                          ~ ( ( r2_hidden @ D @ ( k3_relat_1 @ A ) )
                            & ( r2_hidden @ ( k4_tarski @ B @ D ) @ A )
                            & ( D != B )
                            & ~ ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_wellord1])).

thf('0',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_wellord1 @ X0 )
      | ( v1_relat_2 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('6',plain,
    ( ( v1_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['2','3','8'])).

thf('10',plain,(
    ! [X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X3 ) @ sk_A )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X3 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_D @ sk_B_1 ) ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_D @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['2','3','8'])).

thf('15',plain,(
    ! [X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_B_1 @ X3 ) @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_D @ X3 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_D @ sk_B_1 ) ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_B_1 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ ( k4_tarski @ sk_B_1 @ ( sk_D @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['13','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fw6regVVk3
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:21:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 28 iterations in 0.016s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i).
% 0.20/0.50  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.20/0.50  thf(v1_relat_2_type, type, v1_relat_2: $i > $o).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.20/0.50  thf(v1_wellord1_type, type, v1_wellord1: $i > $o).
% 0.20/0.50  thf(v6_relat_2_type, type, v6_relat_2: $i > $o).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(v4_relat_2_type, type, v4_relat_2: $i > $o).
% 0.20/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.50  thf(t12_wellord1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( v2_wellord1 @ A ) =>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.50                ( ?[C:$i]:
% 0.20/0.50                  ( ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) & 
% 0.20/0.50                    ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) ) ) & 
% 0.20/0.50                ( ![C:$i]:
% 0.20/0.50                  ( ~( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.50                       ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 0.20/0.50                       ( ![D:$i]:
% 0.20/0.50                         ( ~( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.50                              ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) & 
% 0.20/0.50                              ( ( D ) != ( B ) ) & 
% 0.20/0.50                              ( ~( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( v1_relat_1 @ A ) =>
% 0.20/0.50          ( ( v2_wellord1 @ A ) =>
% 0.20/0.50            ( ![B:$i]:
% 0.20/0.50              ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.50                   ( ?[C:$i]:
% 0.20/0.50                     ( ( ~( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) & 
% 0.20/0.50                       ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) ) ) & 
% 0.20/0.50                   ( ![C:$i]:
% 0.20/0.50                     ( ~( ( r2_hidden @ C @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.50                          ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) & 
% 0.20/0.50                          ( ![D:$i]:
% 0.20/0.50                            ( ~( ( r2_hidden @ D @ ( k3_relat_1 @ A ) ) & 
% 0.20/0.50                                 ( r2_hidden @ ( k4_tarski @ B @ D ) @ A ) & 
% 0.20/0.50                                 ( ( D ) != ( B ) ) & 
% 0.20/0.50                                 ( ~( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t12_wellord1])).
% 0.20/0.50  thf('0', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l1_wellord1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( v1_relat_2 @ A ) <=>
% 0.20/0.50         ( ![B:$i]:
% 0.20/0.50           ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) =>
% 0.20/0.50             ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_2 @ X1)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ X2 @ X2) @ X1)
% 0.20/0.50          | ~ (r2_hidden @ X2 @ (k3_relat_1 @ X1))
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [l1_wellord1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_A)
% 0.20/0.50        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ sk_A)
% 0.20/0.50        | ~ (v1_relat_2 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d4_wellord1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( v2_wellord1 @ A ) <=>
% 0.20/0.50         ( ( v1_relat_2 @ A ) & ( v8_relat_2 @ A ) & ( v4_relat_2 @ A ) & 
% 0.20/0.50           ( v6_relat_2 @ A ) & ( v1_wellord1 @ A ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_wellord1 @ X0) | (v1_relat_2 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_wellord1])).
% 0.20/0.50  thf('6', plain, (((v1_relat_2 @ sk_A) | ~ (v2_wellord1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((v2_wellord1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain, ((v1_relat_2 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ (k3_relat_1 @ sk_A))
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_B_1 @ X3) @ sk_A)
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X3)) @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((~ (r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_D @ sk_B_1)) @ sk_A)
% 0.20/0.50        | ~ (r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (~ (r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_D @ sk_B_1)) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, ((r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3', '8'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ (k3_relat_1 @ sk_A))
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ sk_B_1 @ X3) @ sk_A)
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_D @ X3)) @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_D @ sk_B_1)) @ sk_A)
% 0.20/0.50        | ~ (r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((r2_hidden @ sk_B_1 @ (k3_relat_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((r2_hidden @ (k4_tarski @ sk_B_1 @ (sk_D @ sk_B_1)) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain, ($false), inference('demod', [status(thm)], ['13', '18'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
