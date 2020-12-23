%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hXYMq7kLga

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  302 ( 547 expanded)
%              Number of equality atoms :    9 (  27 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_subset_1 @ X7 @ X6 )
      | ( X7 != X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('7',plain,(
    ! [X6: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( v1_subset_1 @ X6 @ X6 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( m1_pre_topc @ X2 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( u1_struct_0 @ sk_B )
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

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ( X5
       != ( u1_struct_0 @ X3 ) )
      | ( v1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ~ ( m1_pre_topc @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','25','26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['8','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hXYMq7kLga
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 21 iterations in 0.015s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(t15_tex_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.48                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( l1_pre_topc @ A ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.48                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.22/0.48  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(l17_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48           ( m1_subset_1 @
% 0.22/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X8 @ X9)
% 0.22/0.48          | (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.48          | ~ (l1_pre_topc @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [l17_tex_2])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('4', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.22/0.48  thf(d7_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (v1_subset_1 @ X7 @ X6)
% 0.22/0.48          | ((X7) != (X6))
% 0.22/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X6 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6)) | ~ (v1_subset_1 @ X6 @ X6))),
% 0.22/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.48  thf(t2_tsep_1, axiom,
% 0.22/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X2 : $i]: ((m1_pre_topc @ X2 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X8 @ X9)
% 0.22/0.48          | (m1_subset_1 @ (u1_struct_0 @ X8) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.48          | ~ (l1_pre_topc @ X9))),
% 0.22/0.48      inference('cnf', [status(esa)], [l17_tex_2])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X0)
% 0.22/0.48          | ~ (l1_pre_topc @ X0)
% 0.22/0.48          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.48          | ~ (l1_pre_topc @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.48  thf('13', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d3_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.48             ( ![C:$i]:
% 0.22/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.48                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X3 @ X4)
% 0.22/0.48          | ~ (v1_tex_2 @ X3 @ X4)
% 0.22/0.48          | ((X5) != (u1_struct_0 @ X3))
% 0.22/0.48          | (v1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.22/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.48          | ~ (l1_pre_topc @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X4)
% 0.22/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X3) @ 
% 0.22/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.48          | (v1_subset_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X4))
% 0.22/0.48          | ~ (v1_tex_2 @ X3 @ X4)
% 0.22/0.48          | ~ (m1_pre_topc @ X3 @ X4))),
% 0.22/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.48          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.22/0.48          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '15'])).
% 0.22/0.48  thf('17', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.48          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.48          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.48        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.22/0.48        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.22/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '19'])).
% 0.22/0.48  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_m1_pre_topc, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X0 @ X1) | (l1_pre_topc @ X0) | ~ (l1_pre_topc @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.48  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['20', '25', '26', '27'])).
% 0.22/0.48  thf('29', plain, ($false), inference('demod', [status(thm)], ['8', '28'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
