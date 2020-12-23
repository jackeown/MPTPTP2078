%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vuJAnKVeXK

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:03 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 111 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  543 ( 914 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_xboole_0 @ sk_B_2 ),
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
    sk_B_2 = k1_xboole_0 ),
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
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_tex_2 @ X15 @ X16 )
      | ~ ( v2_tex_2 @ X17 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( X15 = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vuJAnKVeXK
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.54  % Solved by: fo/fo7.sh
% 0.35/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.54  % done 95 iterations in 0.073s
% 0.35/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.54  % SZS output start Refutation
% 0.35/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.35/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.54  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.35/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.35/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.35/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.54  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.35/0.54  thf(t46_tex_2, conjecture,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( ( v1_xboole_0 @ B ) & 
% 0.35/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.35/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.54    (~( ![A:$i]:
% 0.35/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.54            ( l1_pre_topc @ A ) ) =>
% 0.35/0.54          ( ![B:$i]:
% 0.35/0.54            ( ( ( v1_xboole_0 @ B ) & 
% 0.35/0.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.54              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.35/0.54    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.35/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf(l13_xboole_0, axiom,
% 0.35/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.54  thf('3', plain,
% 0.35/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.35/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.35/0.54  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.54  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['1', '4'])).
% 0.35/0.54  thf(existence_m1_subset_1, axiom,
% 0.35/0.54    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.35/0.54  thf('6', plain, (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.35/0.54      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.35/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.35/0.54  thf('7', plain,
% 0.35/0.54      (![X13 : $i, X14 : $i]:
% 0.35/0.54         ((v1_xboole_0 @ X13)
% 0.35/0.54          | ~ (m1_subset_1 @ X14 @ X13)
% 0.35/0.54          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.35/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.54  thf('8', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.35/0.54          | (v1_xboole_0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf('9', plain, (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.35/0.54      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.35/0.54  thf(t36_tex_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.54           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.35/0.54  thf('10', plain,
% 0.35/0.54      (![X18 : $i, X19 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.35/0.54          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X19) @ X18) @ X19)
% 0.35/0.54          | ~ (l1_pre_topc @ X19)
% 0.35/0.54          | ~ (v2_pre_topc @ X19)
% 0.35/0.54          | (v2_struct_0 @ X19))),
% 0.35/0.54      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.35/0.54  thf('11', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_struct_0 @ X0)
% 0.35/0.54          | ~ (v2_pre_topc @ X0)
% 0.35/0.54          | ~ (l1_pre_topc @ X0)
% 0.35/0.54          | (v2_tex_2 @ 
% 0.35/0.54             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.35/0.54             X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.54  thf('12', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.35/0.54          | ~ (l1_pre_topc @ X0)
% 0.35/0.54          | ~ (v2_pre_topc @ X0)
% 0.35/0.54          | (v2_struct_0 @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['8', '11'])).
% 0.35/0.54  thf('13', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.35/0.54          | (v1_xboole_0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.54  thf('14', plain, (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ X3)),
% 0.35/0.54      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.35/0.54  thf(dt_k6_domain_1, axiom,
% 0.35/0.54    (![A:$i,B:$i]:
% 0.35/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.54       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.54  thf('15', plain,
% 0.35/0.54      (![X11 : $i, X12 : $i]:
% 0.35/0.54         ((v1_xboole_0 @ X11)
% 0.35/0.54          | ~ (m1_subset_1 @ X12 @ X11)
% 0.35/0.54          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.35/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.35/0.54  thf('16', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.35/0.54          | (v1_xboole_0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.54  thf('17', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.35/0.54          | (v1_xboole_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ X0))),
% 0.35/0.54      inference('sup+', [status(thm)], ['13', '16'])).
% 0.35/0.54  thf('18', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v1_xboole_0 @ X0)
% 0.35/0.54          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.35/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.54  thf(t4_subset_1, axiom,
% 0.35/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.54  thf('19', plain,
% 0.35/0.54      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.35/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.54  thf(d7_tex_2, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( l1_pre_topc @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54           ( ( v3_tex_2 @ B @ A ) <=>
% 0.35/0.54             ( ( v2_tex_2 @ B @ A ) & 
% 0.35/0.54               ( ![C:$i]:
% 0.35/0.54                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.54                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.35/0.54                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.54  thf('20', plain,
% 0.35/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.54          | ~ (v3_tex_2 @ X15 @ X16)
% 0.35/0.54          | ~ (v2_tex_2 @ X17 @ X16)
% 0.35/0.54          | ~ (r1_tarski @ X15 @ X17)
% 0.35/0.54          | ((X15) = (X17))
% 0.35/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.35/0.54          | ~ (l1_pre_topc @ X16))),
% 0.35/0.54      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.35/0.54  thf('21', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X0)
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.54          | ((k1_xboole_0) = (X1))
% 0.35/0.54          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.35/0.54          | ~ (v2_tex_2 @ X1 @ X0)
% 0.35/0.54          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.35/0.54  thf('22', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.35/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.35/0.54  thf('23', plain,
% 0.35/0.54      (![X0 : $i, X1 : $i]:
% 0.35/0.54         (~ (l1_pre_topc @ X0)
% 0.35/0.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.54          | ((k1_xboole_0) = (X1))
% 0.35/0.54          | ~ (v2_tex_2 @ X1 @ X0)
% 0.35/0.54          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.35/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.54  thf('24', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.35/0.54          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.35/0.54          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.35/0.54          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.35/0.54          | ~ (l1_pre_topc @ X0))),
% 0.35/0.54      inference('sup-', [status(thm)], ['18', '23'])).
% 0.35/0.54  thf('25', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_struct_0 @ X0)
% 0.35/0.54          | ~ (v2_pre_topc @ X0)
% 0.35/0.54          | ~ (l1_pre_topc @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.35/0.54          | ~ (l1_pre_topc @ X0)
% 0.35/0.54          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.35/0.54          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['12', '24'])).
% 0.35/0.54  thf('26', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.35/0.54          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.35/0.54          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.35/0.54          | ~ (l1_pre_topc @ X0)
% 0.35/0.54          | ~ (v2_pre_topc @ X0)
% 0.35/0.54          | (v2_struct_0 @ X0))),
% 0.35/0.54      inference('simplify', [status(thm)], ['25'])).
% 0.35/0.54  thf('27', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.54      inference('sup-', [status(thm)], ['5', '26'])).
% 0.35/0.54  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('30', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A)
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.54        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.35/0.54      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.35/0.54  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('32', plain,
% 0.35/0.54      ((((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A))))
% 0.35/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('clc', [status(thm)], ['30', '31'])).
% 0.35/0.54  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.35/0.54  thf('33', plain, (![X2 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X2))),
% 0.35/0.54      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.35/0.54  thf('34', plain,
% 0.35/0.54      ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.35/0.54  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.35/0.54  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['34', '35'])).
% 0.35/0.54  thf(rc7_pre_topc, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.54       ( ?[B:$i]:
% 0.35/0.54         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.54           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.54  thf('37', plain,
% 0.35/0.54      (![X10 : $i]:
% 0.35/0.54         ((m1_subset_1 @ (sk_B_1 @ X10) @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.35/0.54          | ~ (l1_pre_topc @ X10)
% 0.35/0.54          | ~ (v2_pre_topc @ X10)
% 0.35/0.54          | (v2_struct_0 @ X10))),
% 0.35/0.54      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.35/0.54  thf(cc1_subset_1, axiom,
% 0.35/0.54    (![A:$i]:
% 0.35/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.35/0.54       ( ![B:$i]:
% 0.35/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.35/0.54  thf('38', plain,
% 0.35/0.54      (![X5 : $i, X6 : $i]:
% 0.35/0.54         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.35/0.54          | (v1_xboole_0 @ X5)
% 0.35/0.54          | ~ (v1_xboole_0 @ X6))),
% 0.35/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.35/0.54  thf('39', plain,
% 0.35/0.54      (![X0 : $i]:
% 0.35/0.54         ((v2_struct_0 @ X0)
% 0.35/0.54          | ~ (v2_pre_topc @ X0)
% 0.35/0.54          | ~ (l1_pre_topc @ X0)
% 0.35/0.54          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.35/0.54          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.35/0.54      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.54  thf('40', plain,
% 0.35/0.54      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.35/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.35/0.54        | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['36', '39'])).
% 0.35/0.54  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('43', plain, (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.35/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.35/0.54  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('45', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.35/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.35/0.54  thf('46', plain,
% 0.35/0.54      (![X10 : $i]:
% 0.35/0.54         (~ (v1_xboole_0 @ (sk_B_1 @ X10))
% 0.35/0.54          | ~ (l1_pre_topc @ X10)
% 0.35/0.54          | ~ (v2_pre_topc @ X10)
% 0.35/0.54          | (v2_struct_0 @ X10))),
% 0.35/0.54      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.35/0.54  thf('47', plain,
% 0.35/0.54      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.54  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.54  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.35/0.54      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.35/0.54  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
