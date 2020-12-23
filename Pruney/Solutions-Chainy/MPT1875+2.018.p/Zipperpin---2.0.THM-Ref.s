%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tAXWf8osS2

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 101 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  423 ( 889 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_tdlat_3 @ X10 )
      | ( v2_tex_2 @ X9 @ X10 )
      | ( X9
       != ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X10 ) @ X10 )
      | ~ ( v1_tdlat_3 @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X10 ) @ X10 )
      | ~ ( v1_tdlat_3 @ X10 ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ( v2_tex_2 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m2_connsp_2 @ ( k2_struct_0 @ X5 ) @ X5 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t35_connsp_2])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m2_connsp_2 @ ( k2_struct_0 @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_connsp_2 @ C @ A @ B )
             => ( r1_tarski @ B @ C ) ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ X6 @ X8 )
      | ~ ( m2_connsp_2 @ X8 @ X7 @ X6 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t36_connsp_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','34','37'])).

thf('39',plain,
    ( ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','38'])).

thf('40',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tAXWf8osS2
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:12:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 39 iterations in 0.025s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.49  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(t43_tex_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.49         ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.21/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t27_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.21/0.49             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.21/0.49          | ~ (v1_tdlat_3 @ X10)
% 0.21/0.49          | (v2_tex_2 @ X9 @ X10)
% 0.21/0.49          | ((X9) != (u1_struct_0 @ X10))
% 0.21/0.49          | ~ (l1_pre_topc @ X10)
% 0.21/0.49          | (v2_struct_0 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t27_tex_2])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X10)
% 0.21/0.49          | ~ (l1_pre_topc @ X10)
% 0.21/0.49          | (v2_tex_2 @ (u1_struct_0 @ X10) @ X10)
% 0.21/0.49          | ~ (v1_tdlat_3 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.49  thf(dt_k2_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.49  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.49  thf('4', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.49  thf('5', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X10)
% 0.21/0.49          | ~ (l1_pre_topc @ X10)
% 0.21/0.49          | (v2_tex_2 @ (u1_struct_0 @ X10) @ X10)
% 0.21/0.49          | ~ (v1_tdlat_3 @ X10))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf(d3_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X2 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t28_tex_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.49                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.49          | ~ (v2_tex_2 @ X11 @ X12)
% 0.21/0.49          | ~ (r1_tarski @ X13 @ X11)
% 0.21/0.49          | (v2_tex_2 @ X13 @ X12)
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.49          | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | (v2_tex_2 @ X1 @ X0)
% 0.21/0.49          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.49        | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.49  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.49        | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((~ (r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t35_connsp_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( m2_connsp_2 @ ( k2_struct_0 @ A ) @ A @ B ) ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.49          | (m2_connsp_2 @ (k2_struct_0 @ X5) @ X5 @ X4)
% 0.21/0.49          | ~ (l1_pre_topc @ X5)
% 0.21/0.49          | ~ (v2_pre_topc @ X5)
% 0.21/0.49          | (v2_struct_0 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_connsp_2])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.49  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, ((m2_connsp_2 @ (k2_struct_0 @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t36_connsp_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]: ( ( m2_connsp_2 @ C @ A @ B ) => ( r1_tarski @ B @ C ) ) ) ) ) ))).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.49          | (r1_tarski @ X6 @ X8)
% 0.21/0.49          | ~ (m2_connsp_2 @ X8 @ X7 @ X6)
% 0.21/0.49          | ~ (l1_pre_topc @ X7)
% 0.21/0.49          | ~ (v2_pre_topc @ X7)
% 0.21/0.49          | (v2_struct_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t36_connsp_2])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | ~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (r1_tarski @ sk_B @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m2_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (r1_tarski @ sk_B @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.49  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r1_tarski @ sk_B @ X0) | ~ (m2_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '33'])).
% 0.21/0.49  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_l1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('36', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, (~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '34', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((~ (v1_tdlat_3 @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '38'])).
% 0.21/0.49  thf('40', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.49  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
