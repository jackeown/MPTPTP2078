%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aTMqJmDWaY

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:03 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 128 expanded)
%              Number of leaves         :   33 (  51 expanded)
%              Depth                    :   20
%              Number of atoms          :  613 (1058 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['1','4'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
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

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_tex_2 @ X19 @ X20 )
      | ~ ( v2_tex_2 @ X21 @ X20 )
      | ~ ( r1_tarski @ X19 @ X21 )
      | ( X19 = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('42',plain,(
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

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aTMqJmDWaY
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.48/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.65  % Solved by: fo/fo7.sh
% 0.48/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.65  % done 252 iterations in 0.196s
% 0.48/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.65  % SZS output start Refutation
% 0.48/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.48/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.65  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.48/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.65  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.48/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.65  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.48/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.65  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.48/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.65  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.48/0.65  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.48/0.65  thf(t46_tex_2, conjecture,
% 0.48/0.65    (![A:$i]:
% 0.48/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.65       ( ![B:$i]:
% 0.48/0.65         ( ( ( v1_xboole_0 @ B ) & 
% 0.48/0.65             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.65           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.48/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.65    (~( ![A:$i]:
% 0.48/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.65            ( l1_pre_topc @ A ) ) =>
% 0.48/0.65          ( ![B:$i]:
% 0.48/0.65            ( ( ( v1_xboole_0 @ B ) & 
% 0.48/0.65                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.65              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.48/0.65    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.48/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('1', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('2', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf(l13_xboole_0, axiom,
% 0.48/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.65  thf('3', plain,
% 0.48/0.65      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.48/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.48/0.65  thf('4', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.65  thf('5', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.48/0.65      inference('demod', [status(thm)], ['1', '4'])).
% 0.48/0.65  thf(d1_xboole_0, axiom,
% 0.48/0.65    (![A:$i]:
% 0.48/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.65  thf('6', plain,
% 0.48/0.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.48/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.65  thf(t1_subset, axiom,
% 0.48/0.65    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.48/0.65  thf('7', plain,
% 0.48/0.65      (![X9 : $i, X10 : $i]:
% 0.48/0.65         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.48/0.65      inference('cnf', [status(esa)], [t1_subset])).
% 0.48/0.65  thf('8', plain,
% 0.48/0.65      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.65  thf(redefinition_k6_domain_1, axiom,
% 0.48/0.65    (![A:$i,B:$i]:
% 0.48/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.48/0.65       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.48/0.65  thf('9', plain,
% 0.48/0.65      (![X17 : $i, X18 : $i]:
% 0.48/0.65         ((v1_xboole_0 @ X17)
% 0.48/0.65          | ~ (m1_subset_1 @ X18 @ X17)
% 0.48/0.65          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.48/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.48/0.65  thf('10', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v1_xboole_0 @ X0)
% 0.48/0.65          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.48/0.65          | (v1_xboole_0 @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.65  thf('11', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.48/0.65          | (v1_xboole_0 @ X0))),
% 0.48/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.48/0.65  thf('12', plain,
% 0.48/0.65      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.65  thf(t36_tex_2, axiom,
% 0.48/0.65    (![A:$i]:
% 0.48/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.65       ( ![B:$i]:
% 0.48/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.65           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.48/0.65  thf('13', plain,
% 0.48/0.65      (![X22 : $i, X23 : $i]:
% 0.48/0.65         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.48/0.65          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22) @ X23)
% 0.48/0.65          | ~ (l1_pre_topc @ X23)
% 0.48/0.65          | ~ (v2_pre_topc @ X23)
% 0.48/0.65          | (v2_struct_0 @ X23))),
% 0.48/0.65      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.48/0.65  thf('14', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.48/0.65          | (v2_struct_0 @ X0)
% 0.48/0.65          | ~ (v2_pre_topc @ X0)
% 0.48/0.65          | ~ (l1_pre_topc @ X0)
% 0.48/0.65          | (v2_tex_2 @ 
% 0.48/0.65             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 0.48/0.65             X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.48/0.65  thf('15', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.48/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.48/0.65          | ~ (l1_pre_topc @ X0)
% 0.48/0.65          | ~ (v2_pre_topc @ X0)
% 0.48/0.65          | (v2_struct_0 @ X0)
% 0.48/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.48/0.65      inference('sup+', [status(thm)], ['11', '14'])).
% 0.48/0.65  thf('16', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v2_struct_0 @ X0)
% 0.48/0.65          | ~ (v2_pre_topc @ X0)
% 0.48/0.65          | ~ (l1_pre_topc @ X0)
% 0.48/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.48/0.65          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 0.48/0.65      inference('simplify', [status(thm)], ['15'])).
% 0.48/0.65  thf('17', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.48/0.65          | (v1_xboole_0 @ X0))),
% 0.48/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.48/0.65  thf('18', plain,
% 0.48/0.65      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.65  thf(dt_k6_domain_1, axiom,
% 0.48/0.65    (![A:$i,B:$i]:
% 0.48/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.48/0.65       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.65  thf('19', plain,
% 0.48/0.65      (![X15 : $i, X16 : $i]:
% 0.48/0.65         ((v1_xboole_0 @ X15)
% 0.48/0.65          | ~ (m1_subset_1 @ X16 @ X15)
% 0.48/0.65          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.48/0.65      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.48/0.65  thf('20', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v1_xboole_0 @ X0)
% 0.48/0.65          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.48/0.65             (k1_zfmisc_1 @ X0))
% 0.48/0.65          | (v1_xboole_0 @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.65  thf('21', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.48/0.65          | (v1_xboole_0 @ X0))),
% 0.48/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.48/0.65  thf('22', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.48/0.65          | (v1_xboole_0 @ X0)
% 0.48/0.65          | (v1_xboole_0 @ X0))),
% 0.48/0.65      inference('sup+', [status(thm)], ['17', '21'])).
% 0.48/0.65  thf('23', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v1_xboole_0 @ X0)
% 0.48/0.65          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.48/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.48/0.65  thf(t4_subset_1, axiom,
% 0.48/0.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.65  thf('24', plain,
% 0.48/0.65      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.48/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.65  thf(d7_tex_2, axiom,
% 0.48/0.65    (![A:$i]:
% 0.48/0.65     ( ( l1_pre_topc @ A ) =>
% 0.48/0.65       ( ![B:$i]:
% 0.48/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.65           ( ( v3_tex_2 @ B @ A ) <=>
% 0.48/0.65             ( ( v2_tex_2 @ B @ A ) & 
% 0.48/0.65               ( ![C:$i]:
% 0.48/0.65                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.65                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.48/0.65                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.48/0.65  thf('25', plain,
% 0.48/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.65         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.48/0.65          | ~ (v3_tex_2 @ X19 @ X20)
% 0.48/0.65          | ~ (v2_tex_2 @ X21 @ X20)
% 0.48/0.65          | ~ (r1_tarski @ X19 @ X21)
% 0.48/0.65          | ((X19) = (X21))
% 0.48/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.48/0.65          | ~ (l1_pre_topc @ X20))),
% 0.48/0.65      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.48/0.65  thf('26', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         (~ (l1_pre_topc @ X0)
% 0.48/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.65          | ((k1_xboole_0) = (X1))
% 0.48/0.65          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.48/0.65          | ~ (v2_tex_2 @ X1 @ X0)
% 0.48/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.48/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.65  thf('27', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.48/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.65  thf('28', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         (~ (l1_pre_topc @ X0)
% 0.48/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.48/0.65          | ((k1_xboole_0) = (X1))
% 0.48/0.65          | ~ (v2_tex_2 @ X1 @ X0)
% 0.48/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.48/0.65      inference('demod', [status(thm)], ['26', '27'])).
% 0.48/0.65  thf('29', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.48/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.48/0.65          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 0.48/0.65          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.48/0.65          | ~ (l1_pre_topc @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['23', '28'])).
% 0.48/0.65  thf('30', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.48/0.65          | ~ (l1_pre_topc @ X0)
% 0.48/0.65          | ~ (v2_pre_topc @ X0)
% 0.48/0.65          | (v2_struct_0 @ X0)
% 0.48/0.65          | ~ (l1_pre_topc @ X0)
% 0.48/0.65          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.48/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.48/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.48/0.65      inference('sup-', [status(thm)], ['16', '29'])).
% 0.48/0.65  thf('31', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.48/0.65          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 0.48/0.65          | (v2_struct_0 @ X0)
% 0.48/0.65          | ~ (v2_pre_topc @ X0)
% 0.48/0.65          | ~ (l1_pre_topc @ X0)
% 0.48/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.48/0.65      inference('simplify', [status(thm)], ['30'])).
% 0.48/0.65  thf('32', plain,
% 0.48/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.48/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.65        | (v2_struct_0 @ sk_A)
% 0.48/0.65        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.65      inference('sup-', [status(thm)], ['5', '31'])).
% 0.48/0.65  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('35', plain,
% 0.48/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.48/0.65        | (v2_struct_0 @ sk_A)
% 0.48/0.65        | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.65      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.48/0.65  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('37', plain,
% 0.48/0.65      ((((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ sk_A))))
% 0.48/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.65      inference('clc', [status(thm)], ['35', '36'])).
% 0.48/0.65  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.48/0.65  thf('38', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X5))),
% 0.48/0.65      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.48/0.65  thf('39', plain,
% 0.48/0.65      ((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.48/0.65  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.65  thf('41', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.48/0.65      inference('demod', [status(thm)], ['39', '40'])).
% 0.48/0.65  thf(rc7_pre_topc, axiom,
% 0.48/0.65    (![A:$i]:
% 0.48/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.65       ( ?[B:$i]:
% 0.48/0.65         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.48/0.65           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.48/0.65  thf('42', plain,
% 0.48/0.65      (![X14 : $i]:
% 0.48/0.65         ((m1_subset_1 @ (sk_B_1 @ X14) @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.48/0.65          | ~ (l1_pre_topc @ X14)
% 0.48/0.65          | ~ (v2_pre_topc @ X14)
% 0.48/0.65          | (v2_struct_0 @ X14))),
% 0.48/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.48/0.65  thf(cc1_subset_1, axiom,
% 0.48/0.65    (![A:$i]:
% 0.48/0.65     ( ( v1_xboole_0 @ A ) =>
% 0.48/0.65       ( ![B:$i]:
% 0.48/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.48/0.65  thf('43', plain,
% 0.48/0.65      (![X7 : $i, X8 : $i]:
% 0.48/0.65         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.48/0.65          | (v1_xboole_0 @ X7)
% 0.48/0.65          | ~ (v1_xboole_0 @ X8))),
% 0.48/0.65      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.48/0.65  thf('44', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         ((v2_struct_0 @ X0)
% 0.48/0.65          | ~ (v2_pre_topc @ X0)
% 0.48/0.65          | ~ (l1_pre_topc @ X0)
% 0.48/0.65          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.48/0.65          | (v1_xboole_0 @ (sk_B_1 @ X0)))),
% 0.48/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.48/0.65  thf('45', plain,
% 0.48/0.65      (((v1_xboole_0 @ (sk_B_1 @ sk_A))
% 0.48/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.65        | (v2_struct_0 @ sk_A))),
% 0.48/0.65      inference('sup-', [status(thm)], ['41', '44'])).
% 0.48/0.65  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('48', plain, (((v1_xboole_0 @ (sk_B_1 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.48/0.65      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.48/0.65  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('50', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_A))),
% 0.48/0.65      inference('clc', [status(thm)], ['48', '49'])).
% 0.48/0.65  thf('51', plain,
% 0.48/0.65      (![X14 : $i]:
% 0.48/0.65         (~ (v1_xboole_0 @ (sk_B_1 @ X14))
% 0.48/0.65          | ~ (l1_pre_topc @ X14)
% 0.48/0.65          | ~ (v2_pre_topc @ X14)
% 0.48/0.65          | (v2_struct_0 @ X14))),
% 0.48/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.48/0.65  thf('52', plain,
% 0.48/0.65      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.48/0.65  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('55', plain, ((v2_struct_0 @ sk_A)),
% 0.48/0.65      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.48/0.65  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 0.48/0.65  
% 0.48/0.65  % SZS output end Refutation
% 0.48/0.65  
% 0.48/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
