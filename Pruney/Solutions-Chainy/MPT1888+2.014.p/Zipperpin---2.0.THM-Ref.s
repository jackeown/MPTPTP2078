%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zHgIhc4RcS

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:29 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 210 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   24
%              Number of atoms          : 1146 (3940 expanded)
%              Number of equality atoms :   18 (  89 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t56_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                | ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                  = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r1_xboole_0 @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                  | ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                    = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t56_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
      | ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('19',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v4_pre_topc @ X18 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X15 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t40_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_xboole_0 @ B @ C )
                  & ( v3_pre_topc @ B @ A ) )
               => ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_xboole_0 @ X19 @ ( k2_pre_topc @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('54',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('55',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['52','58'])).

thf('60',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t55_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
               => ( ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                  = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_hidden @ X22 @ ( k2_pre_topc @ X23 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X24 ) ) )
      | ( ( k2_pre_topc @ X23 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X22 ) )
        = ( k2_pre_topc @ X23 @ ( k6_domain_1 @ ( u1_struct_0 @ X23 ) @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v3_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('76',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('79',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zHgIhc4RcS
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 422 iterations in 0.203s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.46/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.66  thf(t56_tex_2, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.66         ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66               ( ( r1_xboole_0 @
% 0.46/0.66                   ( k2_pre_topc @
% 0.46/0.66                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.46/0.66                   ( k2_pre_topc @
% 0.46/0.66                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.46/0.66                 ( ( k2_pre_topc @
% 0.46/0.66                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.46/0.66                   ( k2_pre_topc @
% 0.46/0.66                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.66            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66                  ( ( r1_xboole_0 @
% 0.46/0.66                      ( k2_pre_topc @
% 0.46/0.66                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.46/0.66                      ( k2_pre_topc @
% 0.46/0.66                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.46/0.66                    ( ( k2_pre_topc @
% 0.46/0.66                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.46/0.66                      ( k2_pre_topc @
% 0.46/0.66                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.46/0.66  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(redefinition_k6_domain_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.66       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ X13)
% 0.46/0.66          | ~ (m1_subset_1 @ X14 @ X13)
% 0.46/0.66          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_k6_domain_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.66       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ X11)
% 0.46/0.66          | ~ (m1_subset_1 @ X12 @ X11)
% 0.46/0.66          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['3', '6'])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.66  thf(l27_zfmisc_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ (k1_tarski @ X5) @ X6) | (r2_hidden @ X5 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.46/0.66  thf(t3_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.66            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X2 @ X0)
% 0.46/0.66          | ~ (r2_hidden @ X2 @ X3)
% 0.46/0.66          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.46/0.66      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X1 @ X0)
% 0.46/0.66          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.66          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.46/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.66          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.46/0.66          | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('sup-', [status(thm)], ['10', '13'])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]:
% 0.46/0.66         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['9', '15'])).
% 0.46/0.66  thf('17', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ X13)
% 0.46/0.66          | ~ (m1_subset_1 @ X14 @ X13)
% 0.46/0.66          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X11 : $i, X12 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ X11)
% 0.46/0.66          | ~ (m1_subset_1 @ X12 @ X11)
% 0.46/0.66          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.46/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['19', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.66  thf(dt_k2_pre_topc, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( m1_subset_1 @
% 0.46/0.66         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X7 : $i, X8 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X7)
% 0.46/0.66          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.46/0.66          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['26', '27'])).
% 0.46/0.66  thf(t24_tdlat_3, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ( v3_tdlat_3 @ A ) <=>
% 0.46/0.66         ( ![B:$i]:
% 0.46/0.66           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i]:
% 0.46/0.66         (~ (v3_tdlat_3 @ X17)
% 0.46/0.66          | ~ (v4_pre_topc @ X18 @ X17)
% 0.46/0.66          | (v3_pre_topc @ X18 @ X17)
% 0.46/0.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.46/0.66          | ~ (l1_pre_topc @ X17)
% 0.46/0.66          | ~ (v2_pre_topc @ X17))),
% 0.46/0.66      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.46/0.66        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.46/0.66        | ~ (v3_tdlat_3 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('33', plain, ((v3_tdlat_3 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.46/0.66        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.66  thf(fc1_tops_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      (![X15 : $i, X16 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X15)
% 0.46/0.66          | ~ (v2_pre_topc @ X15)
% 0.46/0.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.66          | (v4_pre_topc @ (k2_pre_topc @ X15 @ X16) @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.66  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('40', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['34', '40'])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['26', '27'])).
% 0.46/0.66  thf(t40_tsep_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.46/0.66                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('43', plain,
% 0.46/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.66          | ~ (v3_pre_topc @ X19 @ X20)
% 0.46/0.66          | ~ (r1_xboole_0 @ X19 @ X21)
% 0.46/0.66          | (r1_xboole_0 @ X19 @ (k2_pre_topc @ X20 @ X21))
% 0.46/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.66          | ~ (l1_pre_topc @ X20)
% 0.46/0.66          | ~ (v2_pre_topc @ X20))),
% 0.46/0.66      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.46/0.66          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.46/0.66          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.46/0.66          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '47'])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ X0))
% 0.46/0.66          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.46/0.66          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['48'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.46/0.66          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.46/0.66          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.46/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '49'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r2_hidden @ sk_C_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '50'])).
% 0.46/0.66  thf('52', plain,
% 0.46/0.66      (((r2_hidden @ sk_C_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.46/0.66        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('54', plain,
% 0.46/0.66      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      (~ (r1_xboole_0 @ 
% 0.46/0.66          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.46/0.66          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['53', '56'])).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.46/0.66             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['57'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (r2_hidden @ sk_C_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.46/0.66      inference('clc', [status(thm)], ['52', '58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.66  thf(t55_tex_2, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.66         ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.66               ( ( r2_hidden @
% 0.46/0.66                   B @ 
% 0.46/0.66                   ( k2_pre_topc @
% 0.46/0.66                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.46/0.66                 ( ( k2_pre_topc @
% 0.46/0.66                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.46/0.66                   ( k2_pre_topc @
% 0.46/0.66                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.46/0.66          | ~ (r2_hidden @ X22 @ 
% 0.46/0.66               (k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X24)))
% 0.46/0.66          | ((k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22))
% 0.46/0.66              = (k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X24)))
% 0.46/0.66          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.46/0.66          | ~ (l1_pre_topc @ X23)
% 0.46/0.66          | ~ (v3_tdlat_3 @ X23)
% 0.46/0.66          | ~ (v2_pre_topc @ X23)
% 0.46/0.66          | (v2_struct_0 @ X23))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.46/0.66          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | (v2_struct_0 @ sk_A)
% 0.46/0.66          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66          | ~ (v3_tdlat_3 @ sk_A)
% 0.46/0.66          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.46/0.66              = (k2_pre_topc @ sk_A @ 
% 0.46/0.66                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.66  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('64', plain, ((v3_tdlat_3 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('66', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.46/0.66          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66          | (v2_struct_0 @ sk_A)
% 0.46/0.66          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.46/0.66              = (k2_pre_topc @ sk_A @ 
% 0.46/0.66                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.46/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.46/0.66            = (k2_pre_topc @ sk_A @ 
% 0.46/0.66               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['59', '67'])).
% 0.46/0.66  thf('69', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.46/0.66            = (k2_pre_topc @ sk_A @ 
% 0.46/0.66               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.66  thf('71', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.46/0.66            = (k2_pre_topc @ sk_A @ 
% 0.46/0.66               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['70'])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.46/0.66         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.46/0.66  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('75', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['73', '74'])).
% 0.46/0.66  thf(fc2_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.66       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (![X10 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.46/0.66          | ~ (l1_struct_0 @ X10)
% 0.46/0.66          | (v2_struct_0 @ X10))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.66  thf('77', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.66  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_l1_pre_topc, axiom,
% 0.46/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.66  thf('79', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.66  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.66  thf('81', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['77', '80'])).
% 0.46/0.66  thf('82', plain, ($false), inference('demod', [status(thm)], ['0', '81'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
