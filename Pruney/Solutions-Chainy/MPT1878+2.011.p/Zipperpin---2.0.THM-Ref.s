%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1IlPQpxRpX

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:04 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 115 expanded)
%              Number of leaves         :   33 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  555 ( 909 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_2 = k1_xboole_0 ),
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
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_tex_2 @ X17 @ X18 )
      | ~ ( v2_tex_2 @ X19 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( X17 = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
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
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
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
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','29'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['36','37'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1IlPQpxRpX
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.57/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.77  % Solved by: fo/fo7.sh
% 0.57/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.77  % done 458 iterations in 0.315s
% 0.57/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.77  % SZS output start Refutation
% 0.57/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.57/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.57/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.57/0.77  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.57/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.77  thf(sk_B_type, type, sk_B: $i > $i).
% 0.57/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.57/0.77  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.57/0.77  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.57/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.57/0.77  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.57/0.77  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.57/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.77  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.57/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.77  thf(t46_tex_2, conjecture,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( ( v1_xboole_0 @ B ) & 
% 0.57/0.77             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.57/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.77    (~( ![A:$i]:
% 0.57/0.77        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.57/0.77            ( l1_pre_topc @ A ) ) =>
% 0.57/0.77          ( ![B:$i]:
% 0.57/0.77            ( ( ( v1_xboole_0 @ B ) & 
% 0.57/0.77                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.57/0.77              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.57/0.77    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.57/0.77  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf(l13_xboole_0, axiom,
% 0.57/0.77    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.57/0.77  thf('1', plain,
% 0.57/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.57/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.57/0.77  thf('2', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('3', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('4', plain,
% 0.57/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.57/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.57/0.77  thf('5', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.57/0.77  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.57/0.77      inference('demod', [status(thm)], ['2', '5'])).
% 0.57/0.77  thf('7', plain,
% 0.57/0.77      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['1', '6'])).
% 0.57/0.77  thf(existence_m1_subset_1, axiom,
% 0.57/0.77    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.57/0.77  thf('8', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.57/0.77      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.57/0.77  thf(redefinition_k6_domain_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.57/0.77       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.57/0.77  thf('9', plain,
% 0.57/0.77      (![X15 : $i, X16 : $i]:
% 0.57/0.77         ((v1_xboole_0 @ X15)
% 0.57/0.77          | ~ (m1_subset_1 @ X16 @ X15)
% 0.57/0.77          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.57/0.77      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.57/0.77  thf('10', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.57/0.77          | (v1_xboole_0 @ X0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['8', '9'])).
% 0.57/0.77  thf('11', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.57/0.77      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.57/0.77  thf(t36_tex_2, axiom,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.57/0.77           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.57/0.77  thf('12', plain,
% 0.57/0.77      (![X20 : $i, X21 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.57/0.77          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.57/0.77          | ~ (l1_pre_topc @ X21)
% 0.57/0.77          | ~ (v2_pre_topc @ X21)
% 0.57/0.77          | (v2_struct_0 @ X21))),
% 0.57/0.77      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.57/0.77  thf('13', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((v2_struct_0 @ X0)
% 0.57/0.77          | ~ (v2_pre_topc @ X0)
% 0.57/0.77          | ~ (l1_pre_topc @ X0)
% 0.57/0.77          | (v2_tex_2 @ 
% 0.57/0.77             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.57/0.77             X0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.57/0.77  thf('14', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.57/0.77          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.57/0.77          | ~ (l1_pre_topc @ X0)
% 0.57/0.77          | ~ (v2_pre_topc @ X0)
% 0.57/0.77          | (v2_struct_0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['10', '13'])).
% 0.57/0.77  thf('15', plain, (![X5 : $i]: (m1_subset_1 @ (sk_B @ X5) @ X5)),
% 0.57/0.77      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.57/0.77  thf(t55_subset_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( m1_subset_1 @ B @ A ) =>
% 0.57/0.77       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.57/0.77         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.57/0.77  thf('16', plain,
% 0.57/0.77      (![X7 : $i, X8 : $i]:
% 0.57/0.77         (((X7) = (k1_xboole_0))
% 0.57/0.77          | ~ (m1_subset_1 @ X8 @ X7)
% 0.57/0.77          | (m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.57/0.77  thf('17', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.57/0.77          | ((X0) = (k1_xboole_0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.57/0.77  thf(t4_subset_1, axiom,
% 0.57/0.77    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.57/0.77  thf('18', plain,
% 0.57/0.77      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.57/0.77      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.57/0.77  thf(d7_tex_2, axiom,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( l1_pre_topc @ A ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77           ( ( v3_tex_2 @ B @ A ) <=>
% 0.57/0.77             ( ( v2_tex_2 @ B @ A ) & 
% 0.57/0.77               ( ![C:$i]:
% 0.57/0.77                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.57/0.77                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.57/0.77                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.57/0.77  thf('19', plain,
% 0.57/0.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.57/0.77          | ~ (v3_tex_2 @ X17 @ X18)
% 0.57/0.77          | ~ (v2_tex_2 @ X19 @ X18)
% 0.57/0.77          | ~ (r1_tarski @ X17 @ X19)
% 0.57/0.77          | ((X17) = (X19))
% 0.57/0.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.57/0.77          | ~ (l1_pre_topc @ X18))),
% 0.57/0.77      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.57/0.77  thf('20', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (~ (l1_pre_topc @ X0)
% 0.57/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.57/0.77          | ((k1_xboole_0) = (X1))
% 0.57/0.77          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.57/0.77          | ~ (v2_tex_2 @ X1 @ X0)
% 0.57/0.77          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.57/0.77  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.57/0.77  thf('21', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 0.57/0.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.57/0.77  thf('22', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (~ (l1_pre_topc @ X0)
% 0.57/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.57/0.77          | ((k1_xboole_0) = (X1))
% 0.57/0.77          | ~ (v2_tex_2 @ X1 @ X0)
% 0.57/0.77          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.57/0.77      inference('demod', [status(thm)], ['20', '21'])).
% 0.57/0.77  thf('23', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.57/0.77          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.57/0.77          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.57/0.77          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.57/0.77          | ~ (l1_pre_topc @ X0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['17', '22'])).
% 0.57/0.77  thf(t1_boole, axiom,
% 0.57/0.77    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.77  thf('24', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [t1_boole])).
% 0.57/0.77  thf(t49_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.57/0.77  thf('25', plain,
% 0.57/0.77      (![X3 : $i, X4 : $i]:
% 0.57/0.77         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.57/0.77  thf('26', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.57/0.77  thf('27', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.57/0.77          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.57/0.77          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.57/0.77          | ~ (l1_pre_topc @ X0))),
% 0.57/0.77      inference('simplify_reflect-', [status(thm)], ['23', '26'])).
% 0.57/0.77  thf('28', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((v2_struct_0 @ X0)
% 0.57/0.77          | ~ (v2_pre_topc @ X0)
% 0.57/0.77          | ~ (l1_pre_topc @ X0)
% 0.57/0.77          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.57/0.77          | ~ (l1_pre_topc @ X0)
% 0.57/0.77          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.57/0.77          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['14', '27'])).
% 0.57/0.77  thf('29', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 0.57/0.77          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.57/0.77          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.57/0.77          | ~ (l1_pre_topc @ X0)
% 0.57/0.77          | ~ (v2_pre_topc @ X0)
% 0.57/0.77          | (v2_struct_0 @ X0))),
% 0.57/0.77      inference('simplify', [status(thm)], ['28'])).
% 0.57/0.77  thf('30', plain,
% 0.57/0.77      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.57/0.77        | (v2_struct_0 @ sk_A)
% 0.57/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.77        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['7', '29'])).
% 0.57/0.77  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.57/0.77  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.57/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.57/0.77  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('34', plain,
% 0.57/0.77      (((v2_struct_0 @ sk_A)
% 0.57/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.57/0.77        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.57/0.77  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('36', plain,
% 0.57/0.77      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.57/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.57/0.77      inference('clc', [status(thm)], ['34', '35'])).
% 0.57/0.77  thf('37', plain,
% 0.57/0.77      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.57/0.77      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.57/0.77  thf('38', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.57/0.77      inference('clc', [status(thm)], ['36', '37'])).
% 0.57/0.77  thf(rc7_pre_topc, axiom,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.57/0.77       ( ?[B:$i]:
% 0.57/0.77         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.57/0.77           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.57/0.77  thf('39', plain,
% 0.57/0.77      (![X14 : $i]:
% 0.57/0.77         ((m1_subset_1 @ (sk_B_1 @ X14) @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.57/0.77          | ~ (l1_pre_topc @ X14)
% 0.57/0.77          | ~ (v2_pre_topc @ X14)
% 0.57/0.77          | (v2_struct_0 @ X14))),
% 0.57/0.77      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.57/0.77  thf(cc1_subset_1, axiom,
% 0.57/0.77    (![A:$i]:
% 0.57/0.77     ( ( v1_xboole_0 @ A ) =>
% 0.57/0.77       ( ![B:$i]:
% 0.57/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.57/0.77  thf('40', plain,
% 0.57/0.77      (![X9 : $i, X10 : $i]:
% 0.57/0.77         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.57/0.77          | (v1_xboole_0 @ X9)
% 0.57/0.77          | ~ (v1_xboole_0 @ X10))),
% 0.57/0.77      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.57/0.77  thf('41', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((v2_struct_0 @ X0)
% 0.57/0.77          | ~ (v2_pre_topc @ X0)
% 0.57/0.77          | ~ (l1_pre_topc @ X0)
% 0.57/0.77          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.57/0.77          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['39', '40'])).
% 0.57/0.77  thf('42', plain,
% 0.57/0.77      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.57/0.77        | (v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.57/0.77        | ~ (l1_pre_topc @ sk_A)
% 0.57/0.77        | ~ (v2_pre_topc @ sk_A)
% 0.57/0.77        | (v2_struct_0 @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['38', '41'])).
% 0.57/0.77  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.57/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.57/0.77  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('46', plain, (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.57/0.77      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.57/0.77  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('48', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.57/0.77      inference('clc', [status(thm)], ['46', '47'])).
% 0.57/0.77  thf('49', plain,
% 0.57/0.77      (![X14 : $i]:
% 0.57/0.77         (~ (v1_xboole_0 @ (sk_B_1 @ X14))
% 0.57/0.77          | ~ (l1_pre_topc @ X14)
% 0.57/0.77          | ~ (v2_pre_topc @ X14)
% 0.57/0.77          | (v2_struct_0 @ X14))),
% 0.57/0.77      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.57/0.77  thf('50', plain,
% 0.57/0.77      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.57/0.77      inference('sup-', [status(thm)], ['48', '49'])).
% 0.57/0.77  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('53', plain, ((v2_struct_0 @ sk_A)),
% 0.57/0.77      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.57/0.77  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 0.57/0.77  
% 0.57/0.77  % SZS output end Refutation
% 0.57/0.77  
% 0.57/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
