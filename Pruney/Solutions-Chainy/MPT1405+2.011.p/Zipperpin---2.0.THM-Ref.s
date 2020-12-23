%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r1gQXwDTWq

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  340 ( 678 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t35_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_connsp_2])).

thf('0',plain,(
    ~ ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t43_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X33: $i] :
      ( ( ( k1_tops_1 @ X33 @ ( k2_struct_0 @ X33 ) )
        = ( k2_struct_0 @ X33 ) )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t43_tops_1])).

thf('3',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X28: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( r1_tarski @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( r1_tarski @ X34 @ ( k1_tops_1 @ X35 @ X36 ) )
      | ( m2_connsp_2 @ X36 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    r1_tarski @ sk_B_2 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m2_connsp_2 @ ( u1_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['22','29','30','31'])).

thf('33',plain,
    ( ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_2 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('35',plain,(
    m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r1gQXwDTWq
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 234 iterations in 0.181s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(t35_connsp_2, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.63            ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63              ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t35_connsp_2])).
% 0.46/0.63  thf('0', plain, (~ (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_2)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d3_struct_0, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X31 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf(t43_tops_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X33 : $i]:
% 0.46/0.63         (((k1_tops_1 @ X33 @ (k2_struct_0 @ X33)) = (k2_struct_0 @ X33))
% 0.46/0.63          | ~ (l1_pre_topc @ X33)
% 0.46/0.63          | ~ (v2_pre_topc @ X33))),
% 0.46/0.63      inference('cnf', [status(esa)], [t43_tops_1])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X31 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf(d3_tarski, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X4 : $i, X6 : $i]:
% 0.46/0.63         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X4 : $i, X6 : $i]:
% 0.46/0.63         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.63      inference('simplify', [status(thm)], ['6'])).
% 0.46/0.63  thf(t3_subset, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X28 : $i, X30 : $i]:
% 0.46/0.63         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X30)) | ~ (r1_tarski @ X28 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('9', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d2_connsp_2, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.46/0.63                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.63          | ~ (r1_tarski @ X34 @ (k1_tops_1 @ X35 @ X36))
% 0.46/0.63          | (m2_connsp_2 @ X36 @ X35 @ X34)
% 0.46/0.63          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.46/0.63          | ~ (l1_pre_topc @ X35)
% 0.46/0.63          | ~ (v2_pre_topc @ X35))),
% 0.46/0.63      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v2_pre_topc @ sk_A)
% 0.46/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_2)
% 0.46/0.63          | ~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.63          | (m2_connsp_2 @ X0 @ sk_A @ sk_B_2)
% 0.46/0.63          | ~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ X0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      ((~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.46/0.63        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2))),
% 0.46/0.63      inference('sup-', [status(thm)], ['9', '15'])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      ((~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.63        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2))),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '16'])).
% 0.46/0.63  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(dt_l1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.63  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      ((~ (r1_tarski @ sk_B_2 @ (k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.46/0.63        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2))),
% 0.46/0.63      inference('demod', [status(thm)], ['17', '20'])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      ((~ (r1_tarski @ sk_B_2 @ (k2_struct_0 @ sk_A))
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | (m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2))),
% 0.46/0.63      inference('sup-', [status(thm)], ['2', '21'])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (![X31 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.63  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (![X28 : $i, X29 : $i]:
% 0.46/0.63         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.63  thf('29', plain, ((r1_tarski @ sk_B_2 @ (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('32', plain, ((m2_connsp_2 @ (u1_struct_0 @ sk_A) @ sk_A @ sk_B_2)),
% 0.46/0.63      inference('demod', [status(thm)], ['22', '29', '30', '31'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_2)
% 0.46/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['1', '32'])).
% 0.46/0.63  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.63  thf('35', plain, ((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B_2)),
% 0.46/0.63      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.63  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
