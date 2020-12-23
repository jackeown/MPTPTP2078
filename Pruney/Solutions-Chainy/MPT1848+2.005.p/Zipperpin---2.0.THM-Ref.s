%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xPyIguxehw

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 155 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  316 (1172 expanded)
%              Number of equality atoms :   18 (  92 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc12_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ~ ( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ~ ( v1_subset_1 @ ( k2_struct_0 @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc12_struct_0])).

thf('2',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('14',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('16',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( v1_tex_2 @ X5 @ X6 )
      | ( X7
       != ( u1_struct_0 @ X5 ) )
      | ( v1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_tex_2 @ X5 @ X6 )
      | ~ ( m1_pre_topc @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('29',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('30',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('32',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','30','31','32','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['12','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xPyIguxehw
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 26 iterations in 0.016s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(t15_tex_2, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( l1_pre_topc @ A ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.22/0.51  thf('0', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(fc12_struct_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_struct_0 @ A ) =>
% 0.22/0.51       ( ~( v1_subset_1 @ ( k2_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X2 : $i]:
% 0.22/0.51         (~ (v1_subset_1 @ (k2_struct_0 @ X2) @ (u1_struct_0 @ X2))
% 0.22/0.51          | ~ (l1_struct_0 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc12_struct_0])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_l1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.51  thf('4', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '5'])).
% 0.22/0.51  thf('7', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d3_struct_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('11', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (~ (v1_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '11'])).
% 0.22/0.51  thf('13', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('14', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('15', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('16', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf(d3_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.51             ( ![C:$i]:
% 0.22/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X5 @ X6)
% 0.22/0.51          | ~ (v1_tex_2 @ X5 @ X6)
% 0.22/0.51          | ((X7) != (u1_struct_0 @ X5))
% 0.22/0.51          | (v1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.22/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.51          | ~ (l1_pre_topc @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X6)
% 0.22/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X5) @ 
% 0.22/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.51          | (v1_subset_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X6))
% 0.22/0.51          | ~ (v1_tex_2 @ X5 @ X6)
% 0.22/0.51          | ~ (m1_pre_topc @ X5 @ X6))),
% 0.22/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.51          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.51          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '18'])).
% 0.22/0.51  thf('20', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.51          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.22/0.51          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      ((~ (m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.22/0.51        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.22/0.51        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.22/0.51        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '22'])).
% 0.22/0.51  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t1_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( m1_subset_1 @
% 0.22/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X3 @ X4)
% 0.22/0.51          | (m1_subset_1 @ (u1_struct_0 @ X3) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.51          | ~ (l1_pre_topc @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.51  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('29', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.22/0.51  thf('31', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('32', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      ((v1_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['23', '30', '31', '32', '33'])).
% 0.22/0.51  thf('35', plain, ($false), inference('demod', [status(thm)], ['12', '34'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
