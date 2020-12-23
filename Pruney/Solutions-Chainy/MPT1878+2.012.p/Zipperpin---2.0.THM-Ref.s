%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RHz4uhBjKl

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:04 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 109 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  522 ( 864 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
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

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['0','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RHz4uhBjKl
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:48:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.50/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.74  % Solved by: fo/fo7.sh
% 0.50/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.74  % done 441 iterations in 0.305s
% 0.50/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.74  % SZS output start Refutation
% 0.50/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.74  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.50/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.50/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.74  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.50/0.74  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.50/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.74  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.50/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.74  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.50/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.50/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.74  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.50/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.74  thf(t46_tex_2, conjecture,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( ( v1_xboole_0 @ B ) & 
% 0.50/0.74             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.74           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.50/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.74    (~( ![A:$i]:
% 0.50/0.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.50/0.74            ( l1_pre_topc @ A ) ) =>
% 0.50/0.74          ( ![B:$i]:
% 0.50/0.74            ( ( ( v1_xboole_0 @ B ) & 
% 0.50/0.74                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.74              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.50/0.74    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.50/0.74  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf(l13_xboole_0, axiom,
% 0.50/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.50/0.74  thf('3', plain,
% 0.50/0.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.50/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.50/0.74  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.74  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.50/0.74      inference('demod', [status(thm)], ['1', '4'])).
% 0.50/0.74  thf(existence_m1_subset_1, axiom,
% 0.50/0.74    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.50/0.74  thf('6', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.50/0.74      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.50/0.74  thf(redefinition_k6_domain_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.50/0.74       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.50/0.74  thf('7', plain,
% 0.50/0.74      (![X17 : $i, X18 : $i]:
% 0.50/0.74         ((v1_xboole_0 @ X17)
% 0.50/0.74          | ~ (m1_subset_1 @ X18 @ X17)
% 0.50/0.74          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.50/0.74      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.50/0.74  thf('8', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.50/0.74          | (v1_xboole_0 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.74  thf('9', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.50/0.74      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.50/0.74  thf(t36_tex_2, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.50/0.74           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.50/0.74  thf('10', plain,
% 0.50/0.74      (![X22 : $i, X23 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.50/0.74          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.50/0.74          | ~ (l1_pre_topc @ X23)
% 0.50/0.74          | ~ (v2_pre_topc @ X23)
% 0.50/0.74          | (v2_struct_0 @ X23))),
% 0.50/0.74      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.50/0.74  thf('11', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((v2_struct_0 @ X0)
% 0.50/0.74          | ~ (v2_pre_topc @ X0)
% 0.50/0.74          | ~ (l1_pre_topc @ X0)
% 0.50/0.74          | (v2_tex_2 @ 
% 0.50/0.74             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.50/0.74             X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.74  thf('12', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.50/0.74          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.50/0.74          | ~ (l1_pre_topc @ X0)
% 0.50/0.74          | ~ (v2_pre_topc @ X0)
% 0.50/0.74          | (v2_struct_0 @ X0))),
% 0.50/0.74      inference('sup+', [status(thm)], ['8', '11'])).
% 0.50/0.74  thf('13', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.50/0.74      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.50/0.74  thf(t2_subset, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( m1_subset_1 @ A @ B ) =>
% 0.50/0.74       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.50/0.74  thf('14', plain,
% 0.50/0.74      (![X11 : $i, X12 : $i]:
% 0.50/0.74         ((r2_hidden @ X11 @ X12)
% 0.50/0.74          | (v1_xboole_0 @ X12)
% 0.50/0.74          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.50/0.74      inference('cnf', [status(esa)], [t2_subset])).
% 0.50/0.74  thf('15', plain,
% 0.50/0.74      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.50/0.74  thf(t63_subset_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( r2_hidden @ A @ B ) =>
% 0.50/0.74       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.50/0.74  thf('16', plain,
% 0.50/0.74      (![X7 : $i, X8 : $i]:
% 0.50/0.74         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.50/0.74          | ~ (r2_hidden @ X7 @ X8))),
% 0.50/0.74      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.50/0.74  thf('17', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((v1_xboole_0 @ X0)
% 0.50/0.74          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.74  thf(t4_subset_1, axiom,
% 0.50/0.74    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.50/0.74  thf('18', plain,
% 0.50/0.74      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.50/0.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.50/0.74  thf(d7_tex_2, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( l1_pre_topc @ A ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.74           ( ( v3_tex_2 @ B @ A ) <=>
% 0.50/0.74             ( ( v2_tex_2 @ B @ A ) & 
% 0.50/0.74               ( ![C:$i]:
% 0.50/0.74                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.74                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.50/0.74                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.74  thf('19', plain,
% 0.50/0.74      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.50/0.74          | ~ (v3_tex_2 @ X19 @ X20)
% 0.50/0.74          | ~ (v2_tex_2 @ X21 @ X20)
% 0.50/0.74          | ~ (r1_tarski @ X19 @ X21)
% 0.50/0.74          | ((X19) = (X21))
% 0.50/0.74          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.50/0.74          | ~ (l1_pre_topc @ X20))),
% 0.50/0.74      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.50/0.74  thf('20', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (~ (l1_pre_topc @ X0)
% 0.50/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.50/0.74          | ((k1_xboole_0) = (X1))
% 0.50/0.74          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.50/0.74          | ~ (v2_tex_2 @ X1 @ X0)
% 0.50/0.74          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.74  thf('21', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.50/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.74  thf('22', plain,
% 0.50/0.74      (![X0 : $i, X1 : $i]:
% 0.50/0.74         (~ (l1_pre_topc @ X0)
% 0.50/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.50/0.74          | ((k1_xboole_0) = (X1))
% 0.50/0.74          | ~ (v2_tex_2 @ X1 @ X0)
% 0.50/0.74          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.50/0.74      inference('demod', [status(thm)], ['20', '21'])).
% 0.50/0.74  thf('23', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.50/0.74          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.50/0.74          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.50/0.74          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.50/0.74          | ~ (l1_pre_topc @ X0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['17', '22'])).
% 0.50/0.74  thf(t1_boole, axiom,
% 0.50/0.74    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.74  thf('24', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.50/0.74      inference('cnf', [status(esa)], [t1_boole])).
% 0.50/0.74  thf(t49_zfmisc_1, axiom,
% 0.50/0.74    (![A:$i,B:$i]:
% 0.50/0.74     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.50/0.74  thf('25', plain,
% 0.50/0.74      (![X3 : $i, X4 : $i]:
% 0.50/0.74         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 0.50/0.74      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.50/0.74  thf('26', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.50/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.50/0.74  thf('27', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.50/0.74          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.50/0.74          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.50/0.74          | ~ (l1_pre_topc @ X0))),
% 0.50/0.74      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 0.50/0.74  thf('28', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((v2_struct_0 @ X0)
% 0.50/0.74          | ~ (v2_pre_topc @ X0)
% 0.50/0.74          | ~ (l1_pre_topc @ X0)
% 0.50/0.74          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.50/0.74          | ~ (l1_pre_topc @ X0)
% 0.50/0.74          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.50/0.74          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['12', '27'])).
% 0.50/0.74  thf('29', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.50/0.74          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.50/0.74          | ~ (l1_pre_topc @ X0)
% 0.50/0.74          | ~ (v2_pre_topc @ X0)
% 0.50/0.74          | (v2_struct_0 @ X0))),
% 0.50/0.74      inference('simplify', [status(thm)], ['28'])).
% 0.50/0.74  thf('30', plain,
% 0.50/0.74      (((v2_struct_0 @ sk_A)
% 0.50/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.50/0.74        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['5', '29'])).
% 0.50/0.74  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('33', plain,
% 0.50/0.74      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.74      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.50/0.74  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('35', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.50/0.74      inference('clc', [status(thm)], ['33', '34'])).
% 0.50/0.74  thf(rc7_pre_topc, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.74       ( ?[B:$i]:
% 0.50/0.74         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.50/0.74           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.50/0.74  thf('36', plain,
% 0.50/0.74      (![X16 : $i]:
% 0.50/0.74         ((m1_subset_1 @ (sk_B_1 @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.50/0.74          | ~ (l1_pre_topc @ X16)
% 0.50/0.74          | ~ (v2_pre_topc @ X16)
% 0.50/0.74          | (v2_struct_0 @ X16))),
% 0.50/0.74      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.50/0.74  thf(cc1_subset_1, axiom,
% 0.50/0.74    (![A:$i]:
% 0.50/0.74     ( ( v1_xboole_0 @ A ) =>
% 0.50/0.74       ( ![B:$i]:
% 0.50/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.50/0.74  thf('37', plain,
% 0.50/0.74      (![X9 : $i, X10 : $i]:
% 0.50/0.74         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.50/0.74          | (v1_xboole_0 @ X9)
% 0.50/0.74          | ~ (v1_xboole_0 @ X10))),
% 0.50/0.74      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.50/0.74  thf('38', plain,
% 0.50/0.74      (![X0 : $i]:
% 0.50/0.74         ((v2_struct_0 @ X0)
% 0.50/0.74          | ~ (v2_pre_topc @ X0)
% 0.50/0.74          | ~ (l1_pre_topc @ X0)
% 0.50/0.74          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.50/0.74          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.50/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.74  thf('39', plain,
% 0.50/0.74      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.50/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.50/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.74        | (v2_struct_0 @ sk_A))),
% 0.50/0.74      inference('sup-', [status(thm)], ['35', '38'])).
% 0.50/0.74  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('42', plain, (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.50/0.74      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.50/0.74  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('44', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.50/0.74      inference('clc', [status(thm)], ['42', '43'])).
% 0.50/0.74  thf('45', plain,
% 0.50/0.74      (![X16 : $i]:
% 0.50/0.74         (~ (v1_xboole_0 @ (sk_B_1 @ X16))
% 0.50/0.74          | ~ (l1_pre_topc @ X16)
% 0.50/0.74          | ~ (v2_pre_topc @ X16)
% 0.50/0.74          | (v2_struct_0 @ X16))),
% 0.50/0.74      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.50/0.74  thf('46', plain,
% 0.50/0.74      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.50/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.50/0.74  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.74  thf('49', plain, ((v2_struct_0 @ sk_A)),
% 0.50/0.74      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.50/0.74  thf('50', plain, ($false), inference('demod', [status(thm)], ['0', '49'])).
% 0.50/0.74  
% 0.50/0.74  % SZS output end Refutation
% 0.50/0.74  
% 0.57/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
