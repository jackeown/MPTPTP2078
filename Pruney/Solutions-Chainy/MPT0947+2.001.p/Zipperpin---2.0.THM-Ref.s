%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T0YER79yH0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 409 expanded)
%              Number of equality atoms :    7 (  19 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t12_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r4_wellord1 @ A @ ( k1_wellord2 @ B ) )
                  & ( r4_wellord1 @ A @ ( k1_wellord2 @ C ) ) )
               => ( B = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ( ( ( r4_wellord1 @ A @ ( k1_wellord2 @ B ) )
                    & ( r4_wellord1 @ A @ ( k1_wellord2 @ C ) ) )
                 => ( B = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_wellord2])).

thf('0',plain,(
    r4_wellord1 @ sk_A @ ( k1_wellord2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r4_wellord1 @ sk_A @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ X0 @ X1 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('6',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t52_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( r4_wellord1 @ A @ B )
                  & ( r4_wellord1 @ B @ C ) )
               => ( r4_wellord1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r4_wellord1 @ X3 @ X2 )
      | ~ ( r4_wellord1 @ X2 @ X4 )
      | ( r4_wellord1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t52_wellord1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ X0 )
      | ~ ( r4_wellord1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X5: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('14',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t11_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v3_ordinal1 @ X6 )
      | ( X7 = X6 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X7 ) @ ( k1_wellord2 @ X6 ) )
      | ~ ( v3_ordinal1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_wellord2])).

thf('16',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( sk_B = sk_C )
    | ~ ( v3_ordinal1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B = sk_C ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T0YER79yH0
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:13:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 16 iterations in 0.013s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(t12_wellord2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.47           ( ![C:$i]:
% 0.22/0.47             ( ( v3_ordinal1 @ C ) =>
% 0.22/0.47               ( ( ( r4_wellord1 @ A @ ( k1_wellord2 @ B ) ) & 
% 0.22/0.47                   ( r4_wellord1 @ A @ ( k1_wellord2 @ C ) ) ) =>
% 0.22/0.47                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ A ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( v3_ordinal1 @ B ) =>
% 0.22/0.47              ( ![C:$i]:
% 0.22/0.47                ( ( v3_ordinal1 @ C ) =>
% 0.22/0.47                  ( ( ( r4_wellord1 @ A @ ( k1_wellord2 @ B ) ) & 
% 0.22/0.47                      ( r4_wellord1 @ A @ ( k1_wellord2 @ C ) ) ) =>
% 0.22/0.47                    ( ( B ) = ( C ) ) ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t12_wellord2])).
% 0.22/0.47  thf('0', plain, ((r4_wellord1 @ sk_A @ (k1_wellord2 @ sk_C))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain, ((r4_wellord1 @ sk_A @ (k1_wellord2 @ sk_B))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t50_wellord1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( v1_relat_1 @ B ) =>
% 0.22/0.47           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | (r4_wellord1 @ X0 @ X1)
% 0.22/0.47          | ~ (r4_wellord1 @ X1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.22/0.47        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)
% 0.22/0.47        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.22/0.47  thf('5', plain, (![X5 : $i]: (v1_relat_1 @ (k1_wellord2 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.47  thf('6', plain, ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.47  thf(t52_wellord1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( v1_relat_1 @ B ) =>
% 0.22/0.47           ( ![C:$i]:
% 0.22/0.47             ( ( v1_relat_1 @ C ) =>
% 0.22/0.47               ( ( ( r4_wellord1 @ A @ B ) & ( r4_wellord1 @ B @ C ) ) =>
% 0.22/0.47                 ( r4_wellord1 @ A @ C ) ) ) ) ) ) ))).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X2)
% 0.22/0.47          | ~ (r4_wellord1 @ X3 @ X2)
% 0.22/0.47          | ~ (r4_wellord1 @ X2 @ X4)
% 0.22/0.47          | (r4_wellord1 @ X3 @ X4)
% 0.22/0.47          | ~ (v1_relat_1 @ X4)
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t52_wellord1])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ (k1_wellord2 @ sk_B))
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.22/0.47          | ~ (r4_wellord1 @ sk_A @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.47  thf('9', plain, (![X5 : $i]: (v1_relat_1 @ (k1_wellord2 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.47  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ X0)
% 0.22/0.47          | ~ (r4_wellord1 @ sk_A @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_C))
% 0.22/0.47        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_C)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '11'])).
% 0.22/0.47  thf('13', plain, (![X5 : $i]: (v1_relat_1 @ (k1_wellord2 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_C))),
% 0.22/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf(t11_wellord2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v3_ordinal1 @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( v3_ordinal1 @ B ) =>
% 0.22/0.47           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.22/0.47             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i]:
% 0.22/0.47         (~ (v3_ordinal1 @ X6)
% 0.22/0.47          | ((X7) = (X6))
% 0.22/0.47          | ~ (r4_wellord1 @ (k1_wellord2 @ X7) @ (k1_wellord2 @ X6))
% 0.22/0.47          | ~ (v3_ordinal1 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [t11_wellord2])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      ((~ (v3_ordinal1 @ sk_B) | ((sk_B) = (sk_C)) | ~ (v3_ordinal1 @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain, ((v3_ordinal1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('18', plain, ((v3_ordinal1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('19', plain, (((sk_B) = (sk_C))),
% 0.22/0.47      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.47  thf('20', plain, (((sk_B) != (sk_C))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('21', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
