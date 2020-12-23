%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jxd2DNqsfb

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:16 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   54 (  83 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  490 (1101 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t19_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( ( r1_tarski @ B @ C )
                    & ( v2_tops_2 @ C @ A ) )
                 => ( v2_tops_2 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ( v2_tops_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('9',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t18_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ( v1_tops_2 @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ~ ( v1_tops_2 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C )
          <=> ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X17 @ X18 ) @ X16 )
      | ( r1_tarski @ X18 @ ( k7_setfam_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t52_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ X0 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_C )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k7_setfam_1 @ X15 @ ( k7_setfam_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('25',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v2_tops_2 @ X19 @ X20 )
      | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t16_tops_2])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v2_tops_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_tops_2 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['17','27','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['6','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jxd2DNqsfb
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:06:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.55/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.76  % Solved by: fo/fo7.sh
% 0.55/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.76  % done 924 iterations in 0.318s
% 0.55/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.76  % SZS output start Refutation
% 0.55/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.76  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.55/0.76  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.55/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.76  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.55/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.76  thf(t19_tops_2, conjecture,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( l1_pre_topc @ A ) =>
% 0.55/0.76       ( ![B:$i]:
% 0.55/0.76         ( ( m1_subset_1 @
% 0.55/0.76             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.76           ( ![C:$i]:
% 0.55/0.76             ( ( m1_subset_1 @
% 0.55/0.76                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.76               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.55/0.76                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.55/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.76    (~( ![A:$i]:
% 0.55/0.76        ( ( l1_pre_topc @ A ) =>
% 0.55/0.76          ( ![B:$i]:
% 0.55/0.76            ( ( m1_subset_1 @
% 0.55/0.76                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.76              ( ![C:$i]:
% 0.55/0.76                ( ( m1_subset_1 @
% 0.55/0.76                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.76                  ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.55/0.76                    ( v2_tops_2 @ B @ A ) ) ) ) ) ) ) )),
% 0.55/0.76    inference('cnf.neg', [status(esa)], [t19_tops_2])).
% 0.55/0.76  thf('0', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_B @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(t16_tops_2, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( l1_pre_topc @ A ) =>
% 0.55/0.76       ( ![B:$i]:
% 0.55/0.76         ( ( m1_subset_1 @
% 0.55/0.76             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.76           ( ( v2_tops_2 @ B @ A ) <=>
% 0.55/0.76             ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.55/0.76  thf('1', plain,
% 0.55/0.76      (![X19 : $i, X20 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X19 @ 
% 0.55/0.76             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.55/0.76          | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.55/0.76          | (v2_tops_2 @ X19 @ X20)
% 0.55/0.76          | ~ (l1_pre_topc @ X20))),
% 0.55/0.76      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.55/0.76  thf('2', plain,
% 0.55/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.76        | (v2_tops_2 @ sk_B @ sk_A)
% 0.55/0.76        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.76  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('4', plain,
% 0.55/0.76      (((v2_tops_2 @ sk_B @ sk_A)
% 0.55/0.76        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['2', '3'])).
% 0.55/0.76  thf('5', plain, (~ (v2_tops_2 @ sk_B @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('6', plain,
% 0.55/0.76      (~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.55/0.76      inference('clc', [status(thm)], ['4', '5'])).
% 0.55/0.76  thf('7', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_C @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf(dt_k7_setfam_1, axiom,
% 0.55/0.76    (![A:$i,B:$i]:
% 0.55/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.76       ( m1_subset_1 @
% 0.55/0.76         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.55/0.76  thf('8', plain,
% 0.55/0.76      (![X12 : $i, X13 : $i]:
% 0.55/0.76         ((m1_subset_1 @ (k7_setfam_1 @ X12 @ X13) @ 
% 0.55/0.76           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12)))
% 0.55/0.76          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.55/0.76  thf('9', plain,
% 0.55/0.76      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.76  thf('10', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_B @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('11', plain,
% 0.55/0.76      (![X12 : $i, X13 : $i]:
% 0.55/0.76         ((m1_subset_1 @ (k7_setfam_1 @ X12 @ X13) @ 
% 0.55/0.76           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12)))
% 0.55/0.76          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.55/0.76      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.55/0.76  thf('12', plain,
% 0.55/0.76      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.55/0.76  thf(t18_tops_2, axiom,
% 0.55/0.76    (![A:$i]:
% 0.55/0.76     ( ( l1_pre_topc @ A ) =>
% 0.55/0.76       ( ![B:$i]:
% 0.55/0.76         ( ( m1_subset_1 @
% 0.55/0.76             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.76           ( ![C:$i]:
% 0.55/0.76             ( ( m1_subset_1 @
% 0.55/0.76                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.76               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.55/0.76                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.55/0.76  thf('13', plain,
% 0.55/0.76      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X21 @ 
% 0.55/0.76             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 0.55/0.76          | (v1_tops_2 @ X21 @ X22)
% 0.55/0.76          | ~ (r1_tarski @ X21 @ X23)
% 0.55/0.76          | ~ (v1_tops_2 @ X23 @ X22)
% 0.55/0.76          | ~ (m1_subset_1 @ X23 @ 
% 0.55/0.76               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))
% 0.55/0.76          | ~ (l1_pre_topc @ X22))),
% 0.55/0.76      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.55/0.76  thf('14', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (l1_pre_topc @ sk_A)
% 0.55/0.76          | ~ (m1_subset_1 @ X0 @ 
% 0.55/0.76               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.76          | ~ (v1_tops_2 @ X0 @ sk_A)
% 0.55/0.76          | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.55/0.76          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.55/0.76  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.76  thf('16', plain,
% 0.55/0.76      (![X0 : $i]:
% 0.55/0.76         (~ (m1_subset_1 @ X0 @ 
% 0.55/0.76             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.76          | ~ (v1_tops_2 @ X0 @ sk_A)
% 0.55/0.76          | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.55/0.76          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.55/0.76      inference('demod', [status(thm)], ['14', '15'])).
% 0.55/0.76  thf('17', plain,
% 0.55/0.76      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.55/0.76        | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.55/0.76             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.55/0.76        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.55/0.76      inference('sup-', [status(thm)], ['9', '16'])).
% 0.55/0.76  thf('18', plain,
% 0.55/0.76      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.55/0.76  thf('19', plain,
% 0.55/0.76      ((m1_subset_1 @ sk_C @ 
% 0.55/0.76        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(t52_setfam_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77       ( ![C:$i]:
% 0.55/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C ) <=>
% 0.55/0.77             ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) ))).
% 0.55/0.77  thf('20', plain,
% 0.55/0.77      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17)))
% 0.55/0.77          | ~ (r1_tarski @ (k7_setfam_1 @ X17 @ X18) @ X16)
% 0.55/0.77          | (r1_tarski @ X18 @ (k7_setfam_1 @ X17 @ X16))
% 0.55/0.77          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.55/0.77      inference('cnf', [status(esa)], [t52_setfam_1])).
% 0.55/0.77  thf('21', plain,
% 0.55/0.77      (![X0 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X0 @ 
% 0.55/0.77             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.55/0.77          | (r1_tarski @ X0 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.55/0.77          | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_C))),
% 0.55/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.55/0.77  thf('22', plain,
% 0.55/0.77      ((~ (r1_tarski @ 
% 0.55/0.77           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77            (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.55/0.77           sk_C)
% 0.55/0.77        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.55/0.77           (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.55/0.77      inference('sup-', [status(thm)], ['18', '21'])).
% 0.55/0.77  thf('23', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_B @ 
% 0.55/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf(involutiveness_k7_setfam_1, axiom,
% 0.55/0.77    (![A:$i,B:$i]:
% 0.55/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.77       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.55/0.77  thf('24', plain,
% 0.55/0.77      (![X14 : $i, X15 : $i]:
% 0.55/0.77         (((k7_setfam_1 @ X15 @ (k7_setfam_1 @ X15 @ X14)) = (X14))
% 0.55/0.77          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.55/0.77      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.55/0.77  thf('25', plain,
% 0.55/0.77      (((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.55/0.77         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.55/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.55/0.77  thf('26', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('27', plain,
% 0.55/0.77      ((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.55/0.77        (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.55/0.77      inference('demod', [status(thm)], ['22', '25', '26'])).
% 0.55/0.77  thf('28', plain,
% 0.55/0.77      ((m1_subset_1 @ sk_C @ 
% 0.55/0.77        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('29', plain,
% 0.55/0.77      (![X19 : $i, X20 : $i]:
% 0.55/0.77         (~ (m1_subset_1 @ X19 @ 
% 0.55/0.77             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20))))
% 0.55/0.77          | ~ (v2_tops_2 @ X19 @ X20)
% 0.55/0.77          | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.55/0.77          | ~ (l1_pre_topc @ X20))),
% 0.55/0.77      inference('cnf', [status(esa)], [t16_tops_2])).
% 0.55/0.77  thf('30', plain,
% 0.55/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.77        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.55/0.77        | ~ (v2_tops_2 @ sk_C @ sk_A))),
% 0.55/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.55/0.77  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('32', plain, ((v2_tops_2 @ sk_C @ sk_A)),
% 0.55/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.77  thf('33', plain,
% 0.55/0.77      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)),
% 0.55/0.77      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.55/0.77  thf('34', plain,
% 0.55/0.77      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.55/0.77      inference('demod', [status(thm)], ['17', '27', '33'])).
% 0.55/0.77  thf('35', plain, ($false), inference('demod', [status(thm)], ['6', '34'])).
% 0.55/0.77  
% 0.55/0.77  % SZS output end Refutation
% 0.55/0.77  
% 0.61/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
