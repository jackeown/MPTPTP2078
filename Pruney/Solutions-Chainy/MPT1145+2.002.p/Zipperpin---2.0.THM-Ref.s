%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gf7vPqSNJE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  76 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  302 ( 852 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r7_relat_2_type,type,(
    r7_relat_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t37_orders_2,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ( v6_orders_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ B )
               => ( ( v6_orders_2 @ C @ A )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( ( v6_orders_2 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( v6_orders_2 @ C @ A )
                    & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_orders_2])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_orders_2 @ B @ A )
          <=> ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v6_orders_2 @ X4 @ X5 )
      | ( r7_relat_2 @ ( u1_orders_2 @ X5 ) @ X4 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('7',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B )
    | ~ ( v6_orders_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v6_orders_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t96_orders_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r7_relat_2 @ C @ A )
          & ( r1_tarski @ B @ A ) )
       => ( r7_relat_2 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r7_relat_2 @ X9 @ X7 )
      | ~ ( r7_relat_2 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t96_orders_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r7_relat_2 @ X0 @ sk_B )
      | ( r7_relat_2 @ X0 @ sk_C )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) )
    | ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r7_relat_2 @ ( u1_orders_2 @ X5 ) @ X4 )
      | ( v6_orders_2 @ X4 @ X5 )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_orders_2])).

thf('17',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v6_orders_2 @ sk_C @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v6_orders_2 @ sk_C @ sk_A )
    | ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v6_orders_2 @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v6_orders_2 @ sk_C @ sk_A )
   <= ~ ( v6_orders_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v6_orders_2 @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('26',plain,(
    ~ ( v6_orders_2 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v6_orders_2 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['21','26'])).

thf('28',plain,(
    ~ ( r7_relat_2 @ ( u1_orders_2 @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['19','27'])).

thf('29',plain,(
    ~ ( v1_relat_1 @ ( u1_orders_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','28'])).

thf('30',plain,(
    ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gf7vPqSNJE
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 23 iterations in 0.014s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.47  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r7_relat_2_type, type, r7_relat_2: $i > $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(dt_u1_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( u1_orders_2 @ A ) @ 
% 0.21/0.47         ( k1_zfmisc_1 @
% 0.21/0.47           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X6 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (u1_orders_2 @ X6) @ 
% 0.21/0.47           (k1_zfmisc_1 @ 
% 0.21/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X6))))
% 0.21/0.47          | ~ (l1_orders_2 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.47  thf(cc2_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.47          | (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ 
% 0.21/0.47               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.21/0.47          | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(fc6_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(t37_orders_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( v6_orders_2 @ B @ A ) & 
% 0.21/0.47             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ( r1_tarski @ C @ B ) =>
% 0.21/0.47                 ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.47                   ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( l1_orders_2 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( v6_orders_2 @ B @ A ) & 
% 0.21/0.47                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                  ( ( r1_tarski @ C @ B ) =>
% 0.21/0.47                    ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.47                      ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t37_orders_2])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d11_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( v6_orders_2 @ B @ A ) <=>
% 0.21/0.47             ( r7_relat_2 @ ( u1_orders_2 @ A ) @ B ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.47          | ~ (v6_orders_2 @ X4 @ X5)
% 0.21/0.47          | (r7_relat_2 @ (u1_orders_2 @ X5) @ X4)
% 0.21/0.47          | ~ (l1_orders_2 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [d11_orders_2])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.47        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)
% 0.21/0.47        | ~ (v6_orders_2 @ sk_B @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain, ((v6_orders_2 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, ((r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.47  thf('11', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t96_orders_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ C ) =>
% 0.21/0.47       ( ( ( r7_relat_2 @ C @ A ) & ( r1_tarski @ B @ A ) ) =>
% 0.21/0.47         ( r7_relat_2 @ C @ B ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.47          | ~ (v1_relat_1 @ X9)
% 0.21/0.47          | (r7_relat_2 @ X9 @ X7)
% 0.21/0.47          | ~ (r7_relat_2 @ X9 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t96_orders_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r7_relat_2 @ X0 @ sk_B)
% 0.21/0.47          | (r7_relat_2 @ X0 @ sk_C)
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ (u1_orders_2 @ sk_A))
% 0.21/0.47        | (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.47          | ~ (r7_relat_2 @ (u1_orders_2 @ X5) @ X4)
% 0.21/0.47          | (v6_orders_2 @ X4 @ X5)
% 0.21/0.47          | ~ (l1_orders_2 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [d11_orders_2])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((~ (l1_orders_2 @ sk_A)
% 0.21/0.47        | (v6_orders_2 @ sk_C @ sk_A)
% 0.21/0.47        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((v6_orders_2 @ sk_C @ sk_A)
% 0.21/0.47        | ~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((~ (v6_orders_2 @ sk_C @ sk_A)
% 0.21/0.47        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((~ (v6_orders_2 @ sk_C @ sk_A)) <= (~ ((v6_orders_2 @ sk_C @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.47         <= (~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.47      inference('split', [status(esa)], ['20'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (~ ((v6_orders_2 @ sk_C @ sk_A)) | 
% 0.21/0.47       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('split', [status(esa)], ['20'])).
% 0.21/0.47  thf('26', plain, (~ ((v6_orders_2 @ sk_C @ sk_A))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, (~ (v6_orders_2 @ sk_C @ sk_A)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['21', '26'])).
% 0.21/0.47  thf('28', plain, (~ (r7_relat_2 @ (u1_orders_2 @ sk_A) @ sk_C)),
% 0.21/0.47      inference('clc', [status(thm)], ['19', '27'])).
% 0.21/0.47  thf('29', plain, (~ (v1_relat_1 @ (u1_orders_2 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['14', '28'])).
% 0.21/0.47  thf('30', plain, (~ (l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '29'])).
% 0.21/0.47  thf('31', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('32', plain, ($false), inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
