%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mzq47W3Vqx

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:38 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 309 expanded)
%              Number of leaves         :   31 ( 111 expanded)
%              Depth                    :   20
%              Number of atoms          :  651 (2388 expanded)
%              Number of equality atoms :   22 ( 108 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t66_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ? [B: $i] :
            ( ( v3_tex_2 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_tex_2])).

thf('1',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( v1_subset_1 @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['14','29'])).

thf('31',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t65_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ~ ( ( r1_tarski @ B @ C )
                      & ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ( m1_subset_1 @ ( sk_C @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v3_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X24: $i] :
      ( ~ ( v3_tex_2 @ X24 @ sk_A )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ( v3_tex_2 @ ( sk_C @ X22 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v3_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_tex_2])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ ( sk_C @ X1 @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_tex_2 @ ( sk_C @ X0 @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['53','65'])).

thf('67',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mzq47W3Vqx
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:57:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 304 iterations in 0.160s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.42/0.61  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.61  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf(t66_tex_2, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.42/0.61         ( l1_pre_topc @ A ) ) =>
% 0.42/0.61       ( ?[B:$i]:
% 0.42/0.61         ( ( v3_tex_2 @ B @ A ) & 
% 0.42/0.61           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.61            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61          ( ?[B:$i]:
% 0.42/0.61            ( ( v3_tex_2 @ B @ A ) & 
% 0.42/0.61              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t66_tex_2])).
% 0.42/0.61  thf('1', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t17_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.42/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.42/0.61  thf(t3_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X15 : $i, X17 : $i]:
% 0.42/0.61         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf(d7_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i]:
% 0.42/0.61         (((X19) = (X18))
% 0.42/0.61          | (v1_subset_1 @ X19 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((v1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.42/0.61          | ((k3_xboole_0 @ X0 @ X1) = (X0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.42/0.61  thf(cc4_subset_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( v1_xboole_0 @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X13 : $i, X14 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.42/0.61          | ~ (v1_subset_1 @ X13 @ X14)
% 0.42/0.61          | ~ (v1_xboole_0 @ X14))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X0) | ~ (v1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['6', '9'])).
% 0.42/0.61  thf(t100_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X3 @ X4)
% 0.42/0.61           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k4_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X0 @ X0))
% 0.42/0.61          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['10', '11'])).
% 0.42/0.61  thf(l32_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.42/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k5_xboole_0 @ X0 @ X0) != (k1_xboole_0))
% 0.42/0.61          | ~ (v1_xboole_0 @ X0)
% 0.42/0.61          | (r1_tarski @ X0 @ X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.61  thf(t7_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.42/0.61  thf('15', plain,
% 0.42/0.61      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.42/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.42/0.61  thf(t28_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X7 : $i, X8 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.42/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.42/0.61  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.42/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X7 : $i, X8 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ X3 @ X4)
% 0.42/0.61           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['21', '22'])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.42/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.42/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X0 : $i, X2 : $i]:
% 0.42/0.61         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.61  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['24', '27'])).
% 0.42/0.61  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.42/0.61      inference('sup+', [status(thm)], ['23', '28'])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.42/0.61      inference('simplify_reflect+', [status(thm)], ['14', '29'])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X15 : $i, X17 : $i]:
% 0.42/0.61         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.62  thf(t35_tex_2, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( ( v1_xboole_0 @ B ) & 
% 0.42/0.62             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.62           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X20)
% 0.42/0.62          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.62          | (v2_tex_2 @ X20 @ X21)
% 0.42/0.62          | ~ (l1_pre_topc @ X21)
% 0.42/0.62          | ~ (v2_pre_topc @ X21)
% 0.42/0.62          | (v2_struct_0 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [t35_tex_2])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X1)
% 0.42/0.62          | (v2_struct_0 @ X0)
% 0.42/0.62          | ~ (v2_pre_topc @ X0)
% 0.42/0.62          | ~ (l1_pre_topc @ X0)
% 0.42/0.62          | (v2_tex_2 @ X1 @ X0)
% 0.42/0.62          | ~ (v1_xboole_0 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((v2_tex_2 @ X1 @ X0)
% 0.42/0.62          | ~ (l1_pre_topc @ X0)
% 0.42/0.62          | ~ (v2_pre_topc @ X0)
% 0.42/0.62          | (v2_struct_0 @ X0)
% 0.42/0.62          | ~ (v1_xboole_0 @ X1))),
% 0.42/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0)
% 0.42/0.62          | (v2_struct_0 @ sk_A)
% 0.42/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.42/0.62          | (v2_tex_2 @ X0 @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '35'])).
% 0.42/0.62  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0) | (v2_struct_0 @ sk_A) | (v2_tex_2 @ X0 @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      (![X0 : $i]: ((v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('clc', [status(thm)], ['38', '39'])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.62  thf(t65_tex_2, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.42/0.62         ( l1_pre_topc @ A ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.42/0.62                ( ![C:$i]:
% 0.42/0.62                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.62                    ( ~( ( r1_tarski @ B @ C ) & ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (![X22 : $i, X23 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.62          | ~ (v2_tex_2 @ X22 @ X23)
% 0.42/0.62          | (m1_subset_1 @ (sk_C @ X22 @ X23) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.62          | ~ (l1_pre_topc @ X23)
% 0.42/0.62          | ~ (v3_tdlat_3 @ X23)
% 0.42/0.62          | ~ (v2_pre_topc @ X23)
% 0.42/0.62          | (v2_struct_0 @ X23))),
% 0.42/0.62      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X1)
% 0.42/0.62          | (v2_struct_0 @ X0)
% 0.42/0.62          | ~ (v2_pre_topc @ X0)
% 0.42/0.62          | ~ (v3_tdlat_3 @ X0)
% 0.42/0.62          | ~ (l1_pre_topc @ X0)
% 0.42/0.62          | (m1_subset_1 @ (sk_C @ X1 @ X0) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.42/0.62          | ~ (v2_tex_2 @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.62          | ~ (v3_tdlat_3 @ sk_A)
% 0.42/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.42/0.62          | (v2_struct_0 @ sk_A)
% 0.42/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['40', '43'])).
% 0.42/0.62  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('46', plain, ((v3_tdlat_3 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62          | (v2_struct_0 @ sk_A)
% 0.42/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((v2_struct_0 @ sk_A)
% 0.42/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['48'])).
% 0.42/0.62  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0)
% 0.42/0.62          | (m1_subset_1 @ (sk_C @ X0 @ sk_A) @ 
% 0.42/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('clc', [status(thm)], ['49', '50'])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (![X24 : $i]:
% 0.42/0.62         (~ (v3_tex_2 @ X24 @ sk_A)
% 0.42/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0) | ~ (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      (![X0 : $i]: ((v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('clc', [status(thm)], ['38', '39'])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (![X22 : $i, X23 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.62          | ~ (v2_tex_2 @ X22 @ X23)
% 0.42/0.62          | (v3_tex_2 @ (sk_C @ X22 @ X23) @ X23)
% 0.42/0.62          | ~ (l1_pre_topc @ X23)
% 0.42/0.62          | ~ (v3_tdlat_3 @ X23)
% 0.42/0.62          | ~ (v2_pre_topc @ X23)
% 0.42/0.62          | (v2_struct_0 @ X23))),
% 0.42/0.62      inference('cnf', [status(esa)], [t65_tex_2])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X1)
% 0.42/0.62          | (v2_struct_0 @ X0)
% 0.42/0.62          | ~ (v2_pre_topc @ X0)
% 0.42/0.62          | ~ (v3_tdlat_3 @ X0)
% 0.42/0.62          | ~ (l1_pre_topc @ X0)
% 0.42/0.62          | (v3_tex_2 @ (sk_C @ X1 @ X0) @ X0)
% 0.42/0.62          | ~ (v2_tex_2 @ X1 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0)
% 0.42/0.62          | (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 0.42/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.62          | ~ (v3_tdlat_3 @ sk_A)
% 0.42/0.62          | ~ (v2_pre_topc @ sk_A)
% 0.42/0.62          | (v2_struct_0 @ sk_A)
% 0.42/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['54', '57'])).
% 0.42/0.62  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('60', plain, ((v3_tdlat_3 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0)
% 0.42/0.62          | (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 0.42/0.62          | (v2_struct_0 @ sk_A)
% 0.42/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((v2_struct_0 @ sk_A)
% 0.42/0.62          | (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A)
% 0.42/0.62          | ~ (v1_xboole_0 @ X0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['62'])).
% 0.42/0.62  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (v1_xboole_0 @ X0) | (v3_tex_2 @ (sk_C @ X0 @ sk_A) @ sk_A))),
% 0.42/0.62      inference('clc', [status(thm)], ['63', '64'])).
% 0.42/0.62  thf('66', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.42/0.62      inference('clc', [status(thm)], ['53', '65'])).
% 0.42/0.62  thf('67', plain, ($false), inference('sup-', [status(thm)], ['0', '66'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
