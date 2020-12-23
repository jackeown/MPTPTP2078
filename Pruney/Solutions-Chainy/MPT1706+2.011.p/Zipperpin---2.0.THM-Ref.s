%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2EKoRq2zs

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  183 ( 543 expanded)
%              Number of equality atoms :    3 (  15 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t15_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( m1_pre_topc @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ? [E: $i] :
                        ( ( E = D )
                        & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( m1_pre_topc @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_tmap_1])).

thf('0',plain,(
    ! [X5: $i] :
      ( ( X5 != sk_D )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['1','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B2EKoRq2zs
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 17 iterations in 0.012s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(t15_tmap_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.47               ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.47                 ( ![D:$i]:
% 0.20/0.47                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.47                     ( ?[E:$i]:
% 0.20/0.47                       ( ( ( E ) = ( D ) ) & 
% 0.20/0.47                         ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.47                  ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.47                    ( ![D:$i]:
% 0.20/0.47                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.47                        ( ?[E:$i]:
% 0.20/0.47                          ( ( ( E ) = ( D ) ) & 
% 0.20/0.47                            ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t15_tmap_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X5 : $i]:
% 0.20/0.47         (((X5) != (sk_D)) | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.20/0.47      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.47  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t55_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.47               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X2)
% 0.20/0.47          | ~ (m1_pre_topc @ X2 @ X3)
% 0.20/0.47          | (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 0.20/0.47          | ~ (l1_pre_topc @ X3)
% 0.20/0.47          | (v2_struct_0 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.20/0.47        | ~ (l1_pre_topc @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.47  thf('7', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_m1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.47  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.20/0.47        | (v2_struct_0 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '11'])).
% 0.20/0.47  thf('13', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_C) | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.20/0.47      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('16', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.47  thf('17', plain, ($false), inference('demod', [status(thm)], ['1', '16'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
