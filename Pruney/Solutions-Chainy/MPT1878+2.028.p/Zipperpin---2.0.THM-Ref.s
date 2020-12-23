%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bmLIrwlr2h

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:07 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 117 expanded)
%              Number of leaves         :   35 (  50 expanded)
%              Depth                    :   18
%              Number of atoms          :  555 ( 926 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_3 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('15',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
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

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_tex_2 @ X21 @ X22 )
      | ~ ( v2_tex_2 @ X23 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ( X21 = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B_1 @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_2 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ ( sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_2 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bmLIrwlr2h
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:22:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 252 iterations in 0.188s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.65  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.47/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.47/0.65  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.47/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.47/0.65  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.65  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.47/0.65  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.65  thf(t46_tex_2, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( ( v1_xboole_0 @ B ) & 
% 0.47/0.65             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.65           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.47/0.65            ( l1_pre_topc @ A ) ) =>
% 0.47/0.65          ( ![B:$i]:
% 0.47/0.65            ( ( ( v1_xboole_0 @ B ) & 
% 0.47/0.65                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.47/0.65              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 0.47/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(d1_xboole_0, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.65  thf('1', plain,
% 0.47/0.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.65  thf('2', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('3', plain, ((v1_xboole_0 @ sk_B_3)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf(l13_xboole_0, axiom,
% 0.47/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.65  thf('4', plain,
% 0.47/0.65      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.65  thf('5', plain, (((sk_B_3) = (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.65  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.47/0.65      inference('demod', [status(thm)], ['2', '5'])).
% 0.47/0.65  thf(existence_m1_subset_1, axiom,
% 0.47/0.65    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.47/0.65  thf('7', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B_1 @ X8) @ X8)),
% 0.47/0.65      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.47/0.65  thf(redefinition_k6_domain_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.47/0.65       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      (![X19 : $i, X20 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ X19)
% 0.47/0.65          | ~ (m1_subset_1 @ X20 @ X19)
% 0.47/0.65          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.47/0.65      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.47/0.65  thf('9', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.47/0.65          | (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.65  thf('10', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B_1 @ X8) @ X8)),
% 0.47/0.65      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.47/0.65  thf(t36_tex_2, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.47/0.65           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X24 : $i, X25 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.47/0.65          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24) @ X25)
% 0.47/0.65          | ~ (l1_pre_topc @ X25)
% 0.47/0.65          | ~ (v2_pre_topc @ X25)
% 0.47/0.65          | (v2_struct_0 @ X25))),
% 0.47/0.65      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v2_tex_2 @ 
% 0.47/0.65             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B_1 @ (u1_struct_0 @ X0))) @ 
% 0.47/0.65             X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_tex_2 @ (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))) @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['9', '12'])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.47/0.65          | (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.65  thf('15', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B_1 @ X8) @ X8)),
% 0.47/0.65      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.47/0.65  thf(dt_k6_domain_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.47/0.65       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.65  thf('16', plain,
% 0.47/0.65      (![X17 : $i, X18 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ X17)
% 0.47/0.65          | ~ (m1_subset_1 @ X18 @ X17)
% 0.47/0.65          | (m1_subset_1 @ (k6_domain_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17)))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B_1 @ X0)) @ 
% 0.47/0.65           (k1_zfmisc_1 @ X0))
% 0.47/0.65          | (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (k1_tarski @ (sk_B_1 @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.47/0.65          | (v1_xboole_0 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['14', '17'])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ X0)
% 0.47/0.65          | (m1_subset_1 @ (k1_tarski @ (sk_B_1 @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.47/0.65      inference('simplify', [status(thm)], ['18'])).
% 0.47/0.65  thf(t4_subset_1, axiom,
% 0.47/0.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.47/0.65  thf(d7_tex_2, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( l1_pre_topc @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65           ( ( v3_tex_2 @ B @ A ) <=>
% 0.47/0.65             ( ( v2_tex_2 @ B @ A ) & 
% 0.47/0.65               ( ![C:$i]:
% 0.47/0.65                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.47/0.65                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.47/0.65                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.65         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.47/0.65          | ~ (v3_tex_2 @ X21 @ X22)
% 0.47/0.65          | ~ (v2_tex_2 @ X23 @ X22)
% 0.47/0.65          | ~ (r1_tarski @ X21 @ X23)
% 0.47/0.65          | ((X21) = (X23))
% 0.47/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.47/0.65          | ~ (l1_pre_topc @ X22))),
% 0.47/0.65      inference('cnf', [status(esa)], [d7_tex_2])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.65          | ((k1_xboole_0) = (X1))
% 0.47/0.65          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 0.47/0.65          | ~ (v2_tex_2 @ X1 @ X0)
% 0.47/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.65  thf('23', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.47/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.65  thf('24', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.47/0.65          | ((k1_xboole_0) = (X1))
% 0.47/0.65          | ~ (v2_tex_2 @ X1 @ X0)
% 0.47/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['22', '23'])).
% 0.47/0.65  thf('25', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.47/0.65          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))) @ X0)
% 0.47/0.65          | ((k1_xboole_0) = (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))))
% 0.47/0.65          | ~ (l1_pre_topc @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['19', '24'])).
% 0.47/0.65  thf(t1_boole, axiom,
% 0.47/0.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.65  thf('26', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.47/0.65      inference('cnf', [status(esa)], [t1_boole])).
% 0.47/0.65  thf(t49_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      (![X6 : $i, X7 : $i]:
% 0.47/0.65         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.47/0.65  thf('28', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.47/0.65          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B_1 @ (u1_struct_0 @ X0))) @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0))),
% 0.47/0.65      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 0.47/0.65  thf('30', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['13', '29'])).
% 0.47/0.65  thf('31', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | (v2_struct_0 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['30'])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A)
% 0.47/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['6', '31'])).
% 0.47/0.65  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.47/0.65      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.47/0.65  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('37', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.47/0.65      inference('clc', [status(thm)], ['35', '36'])).
% 0.47/0.65  thf(rc7_pre_topc, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.47/0.65       ( ?[B:$i]:
% 0.47/0.65         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.47/0.65           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (![X16 : $i]:
% 0.47/0.65         ((m1_subset_1 @ (sk_B_2 @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.47/0.65          | ~ (l1_pre_topc @ X16)
% 0.47/0.65          | ~ (v2_pre_topc @ X16)
% 0.47/0.65          | (v2_struct_0 @ X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.47/0.65  thf(t5_subset, axiom,
% 0.47/0.65    (![A:$i,B:$i,C:$i]:
% 0.47/0.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.47/0.65          ( v1_xboole_0 @ C ) ) ))).
% 0.47/0.65  thf('39', plain,
% 0.47/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X13 @ X14)
% 0.47/0.65          | ~ (v1_xboole_0 @ X15)
% 0.47/0.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.47/0.65  thf('40', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((v2_struct_0 @ X0)
% 0.47/0.65          | ~ (v2_pre_topc @ X0)
% 0.47/0.65          | ~ (l1_pre_topc @ X0)
% 0.47/0.65          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.47/0.65          | ~ (r2_hidden @ X1 @ (sk_B_2 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X0 @ (sk_B_2 @ sk_A))
% 0.47/0.65          | ~ (l1_pre_topc @ sk_A)
% 0.47/0.65          | ~ (v2_pre_topc @ sk_A)
% 0.47/0.65          | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['37', '40'])).
% 0.47/0.65  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X0 @ (sk_B_2 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.47/0.65      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.47/0.65  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_2 @ sk_A))),
% 0.47/0.65      inference('clc', [status(thm)], ['44', '45'])).
% 0.47/0.65  thf('47', plain, ((v1_xboole_0 @ (sk_B_2 @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['1', '46'])).
% 0.47/0.65  thf('48', plain,
% 0.47/0.65      (![X16 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ (sk_B_2 @ X16))
% 0.47/0.65          | ~ (l1_pre_topc @ X16)
% 0.47/0.65          | ~ (v2_pre_topc @ X16)
% 0.47/0.65          | (v2_struct_0 @ X16))),
% 0.47/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.47/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.65  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('52', plain, ((v2_struct_0 @ sk_A)),
% 0.47/0.65      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.47/0.65  thf('53', plain, ($false), inference('demod', [status(thm)], ['0', '52'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
