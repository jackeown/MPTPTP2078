%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SKbsKbB9MW

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:08 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 107 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  486 ( 794 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
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

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_tex_2 @ X16 @ X17 )
      | ~ ( v2_tex_2 @ X18 @ X17 )
      | ~ ( r1_tarski @ X16 @ X18 )
      | ( X16 = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','32'])).

thf('34',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('42',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SKbsKbB9MW
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:05:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 305 iterations in 0.215s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.45/0.67  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.45/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.67  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(t46_tex_2, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( ( v1_xboole_0 @ B ) & 
% 0.45/0.67             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.67           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.67            ( l1_pre_topc @ A ) ) =>
% 0.45/0.67          ( ![B:$i]:
% 0.45/0.67            ( ( ( v1_xboole_0 @ B ) & 
% 0.45/0.67                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.67              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.45/0.67  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(l13_xboole_0, axiom,
% 0.45/0.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.67  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.67  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.45/0.67      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['1', '6'])).
% 0.45/0.67  thf(existence_m1_subset_1, axiom,
% 0.45/0.67    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.45/0.67  thf('8', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.45/0.67      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.45/0.67  thf(redefinition_k6_domain_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.45/0.67       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         ((v1_xboole_0 @ X14)
% 0.45/0.67          | ~ (m1_subset_1 @ X15 @ X14)
% 0.45/0.67          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.45/0.67          | (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('11', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.45/0.67      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.45/0.67  thf(t36_tex_2, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.67           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X19 : $i, X20 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.45/0.67          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.45/0.67          | ~ (l1_pre_topc @ X20)
% 0.45/0.67          | ~ (v2_pre_topc @ X20)
% 0.45/0.67          | (v2_struct_0 @ X20))),
% 0.45/0.67      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | (v2_tex_2 @ 
% 0.45/0.67             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.45/0.67             X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.45/0.67          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['10', '13'])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.45/0.67          | (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('16', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.45/0.67      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.45/0.67  thf(dt_k6_domain_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.45/0.67       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i]:
% 0.45/0.67         ((v1_xboole_0 @ X12)
% 0.45/0.67          | ~ (m1_subset_1 @ X13 @ X12)
% 0.45/0.67          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.45/0.67          | (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.45/0.67          | (v1_xboole_0 @ X0)
% 0.45/0.67          | (v1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['15', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v1_xboole_0 @ X0)
% 0.45/0.67          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.67  thf(t4_subset_1, axiom,
% 0.45/0.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.67  thf(d7_tex_2, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( l1_pre_topc @ A ) =>
% 0.45/0.67       ( ![B:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67           ( ( v3_tex_2 @ B @ A ) <=>
% 0.45/0.67             ( ( v2_tex_2 @ B @ A ) & 
% 0.45/0.67               ( ![C:$i]:
% 0.45/0.67                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.67                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.45/0.67                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.67         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.67          | ~ (v3_tex_2 @ X16 @ X17)
% 0.45/0.67          | ~ (v2_tex_2 @ X18 @ X17)
% 0.45/0.67          | ~ (r1_tarski @ X16 @ X18)
% 0.45/0.67          | ((X16) = (X18))
% 0.45/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.45/0.67          | ~ (l1_pre_topc @ X17))),
% 0.45/0.67      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.67          | ((k1_xboole_0) = (X1))
% 0.45/0.67          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.45/0.67          | ~ (v2_tex_2 @ X1 @ X0)
% 0.45/0.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.67  thf('24', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.45/0.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.45/0.67          | ((k1_xboole_0) = (X1))
% 0.45/0.67          | ~ (v2_tex_2 @ X1 @ X0)
% 0.45/0.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['23', '24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.45/0.67          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.45/0.67          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.45/0.67          | ~ (l1_pre_topc @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['20', '25'])).
% 0.45/0.67  thf(t1_boole, axiom,
% 0.45/0.67    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.67  thf('27', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.67  thf(t49_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X3 : $i, X4 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.45/0.67  thf('29', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.45/0.67          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.45/0.67          | ~ (l1_pre_topc @ X0))),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['26', '29'])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v2_struct_0 @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.45/0.67          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '30'])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.45/0.67          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.67          | ~ (l1_pre_topc @ X0)
% 0.45/0.67          | ~ (v2_pre_topc @ X0)
% 0.45/0.67          | (v2_struct_0 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.67        | (v2_struct_0 @ sk_A)
% 0.45/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['7', '32'])).
% 0.45/0.67  thf('34', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('35', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.67  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.67  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.67      inference('demod', [status(thm)], ['33', '36', '37', '38'])).
% 0.45/0.67  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('41', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.67      inference('clc', [status(thm)], ['39', '40'])).
% 0.45/0.67  thf(fc2_struct_0, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.67       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      (![X11 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X11))
% 0.45/0.67          | ~ (l1_struct_0 @ X11)
% 0.45/0.67          | (v2_struct_0 @ X11))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.67  thf('43', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.67  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(dt_l1_pre_topc, axiom,
% 0.45/0.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.45/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.67  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.67      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.67  thf('47', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.67      inference('demod', [status(thm)], ['43', '46'])).
% 0.45/0.67  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
