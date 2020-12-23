%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EtI5T8J7UA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 (  93 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  475 ( 702 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(t46_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( v3_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','4'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v3_tex_2 @ X14 @ X15 )
      | ~ ( v2_tex_2 @ X16 @ X15 )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ( X14 = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('37',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('40',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EtI5T8J7UA
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 62 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.50  thf(t46_tex_2, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.50                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l13_xboole_0, axiom,
% 0.20/0.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.50  thf('4', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.50  thf(existence_m1_subset_1, axiom,
% 0.20/0.50    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.20/0.50  thf('6', plain, (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.20/0.50      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X12)
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ X12)
% 0.20/0.50          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.50          | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.20/0.50      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.50  thf(t36_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.50           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.20/0.50          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X17) @ X18)
% 0.20/0.50          | ~ (l1_pre_topc @ X18)
% 0.20/0.50          | ~ (v2_pre_topc @ X18)
% 0.20/0.50          | (v2_struct_0 @ X18))),
% 0.20/0.50      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_tex_2 @ 
% 0.20/0.50             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.20/0.50             X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.20/0.50          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.20/0.50          | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('14', plain, (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.20/0.50      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.50  thf(dt_k6_domain_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X10)
% 0.20/0.50          | ~ (m1_subset_1 @ X11 @ X10)
% 0.20/0.50          | (m1_subset_1 @ (k6_domain_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.20/0.50          | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.20/0.50          | (v1_xboole_0 @ X0)
% 0.20/0.50          | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['13', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X0)
% 0.20/0.50          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.50  thf(t4_subset_1, axiom,
% 0.20/0.50    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.50  thf(d7_tex_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v3_tex_2 @ B @ A ) <=>
% 0.20/0.50             ( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.50               ( ![C:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.50                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.50          | ~ (v3_tex_2 @ X14 @ X15)
% 0.20/0.50          | ~ (v2_tex_2 @ X16 @ X15)
% 0.20/0.50          | ~ (r1_tarski @ X14 @ X16)
% 0.20/0.50          | ((X14) = (X16))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.50          | ~ (l1_pre_topc @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ((k1_xboole_0) = (X1))
% 0.20/0.50          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.20/0.50          | ~ (v2_tex_2 @ X1 @ X0)
% 0.20/0.50          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.50  thf('22', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ((k1_xboole_0) = (X1))
% 0.20/0.50          | ~ (v2_tex_2 @ X1 @ X0)
% 0.20/0.50          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.50          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.20/0.50          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.20/0.50          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.50          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.20/0.50          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.20/0.50          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '26'])).
% 0.20/0.50  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.50        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.50  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A))))
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.20/0.50  thf('33', plain, (![X2 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.50  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf(fc2_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X9 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.20/0.50          | ~ (l1_struct_0 @ X9)
% 0.20/0.50          | (v2_struct_0 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.50  thf('38', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_l1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('40', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '41'])).
% 0.20/0.50  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
