%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E646IVBgVT

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  234 ( 352 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('1',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7 = X6 )
      | ( v1_subset_1 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t15_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ~ ( ( ( u1_struct_0 @ B )
                = ( u1_struct_0 @ A ) )
              & ( v1_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ~ ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ A ) )
                & ( v1_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_tex_2])).

thf('7',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ( X5
       != ( u1_struct_0 @ X3 ) )
      | ( v1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ~ ( m1_pre_topc @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    v1_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('18',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('20',plain,(
    ! [X1: $i] :
      ~ ( v1_subset_1 @ X1 @ X1 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    $false ),
    inference('sup-',[status(thm)],['17','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E646IVBgVT
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 19 iterations in 0.012s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.47  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.47  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.47  thf(rc3_subset_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ?[B:$i]:
% 0.22/0.47       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.22/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      (![X2 : $i]: (m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X2 : $i]: (m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.22/0.47  thf(d7_subset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.47       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i]:
% 0.22/0.47         (((X7) = (X6))
% 0.22/0.47          | (v1_subset_1 @ X7 @ X6)
% 0.22/0.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.47      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf('4', plain, (![X2 : $i]: ~ (v1_subset_1 @ (sk_B @ X2) @ X2)),
% 0.22/0.47      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.22/0.47  thf('5', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.22/0.47      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.47  thf('6', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '5'])).
% 0.22/0.47  thf(t15_tex_2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( l1_pre_topc @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.47           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.47                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( l1_pre_topc @ A ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.47              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.47                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.22/0.47  thf('7', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(d3_tex_2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( l1_pre_topc @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.47           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.47             ( ![C:$i]:
% 0.22/0.47               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.47                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.47         (~ (m1_pre_topc @ X3 @ X4)
% 0.22/0.47          | ~ (v1_tex_2 @ X3 @ X4)
% 0.22/0.47          | ((X5) != (u1_struct_0 @ X3))
% 0.22/0.47          | (v1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.22/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.47          | ~ (l1_pre_topc @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ X4)
% 0.22/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X3) @ 
% 0.22/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.47          | (v1_subset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X4))
% 0.22/0.47          | ~ (v1_tex_2 @ X3 @ X4)
% 0.22/0.47          | ~ (m1_pre_topc @ X3 @ X4))),
% 0.22/0.47      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.22/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.47          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.47          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.22/0.47          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '9'])).
% 0.22/0.47  thf('11', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.22/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.47          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.47          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))),
% 0.22/0.47      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      (((v1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))
% 0.22/0.47        | ~ (v1_tex_2 @ sk_B_1 @ sk_A)
% 0.22/0.47        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['6', '13'])).
% 0.22/0.47  thf('15', plain, ((v1_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('16', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      ((v1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.22/0.47  thf(fc14_subset_1, axiom,
% 0.22/0.47    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.22/0.47  thf('18', plain, (![X1 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X1) @ X1)),
% 0.22/0.47      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.22/0.47  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.47  thf('19', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.22/0.47      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.47  thf('20', plain, (![X1 : $i]: ~ (v1_subset_1 @ X1 @ X1)),
% 0.22/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('21', plain, ($false), inference('sup-', [status(thm)], ['17', '20'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
