%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dY6cl1ojEz

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:30 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 240 expanded)
%              Number of leaves         :   33 (  81 expanded)
%              Depth                    :   26
%              Number of atoms          : 1278 (4545 expanded)
%              Number of equality atoms :   27 ( 109 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_pre_topc @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
       != X13 )
      | ( v4_pre_topc @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_pre_topc @ X11 @ ( k2_pre_topc @ X11 @ X12 ) )
        = ( k2_pre_topc @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('40',plain,
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

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
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

thf('50',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X23 )
      | ( r1_xboole_0 @ X21 @ ( k2_pre_topc @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('61',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('62',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['59','65'])).

thf('67',plain,
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

thf('68',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ ( k2_pre_topc @ X25 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X26 ) ) )
      | ( ( k2_pre_topc @ X25 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) )
        = ( k2_pre_topc @ X25 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v3_tdlat_3 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('69',plain,(
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
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('83',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('86',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dY6cl1ojEz
% 0.12/0.36  % Computer   : n013.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 20:01:25 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.84/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.05  % Solved by: fo/fo7.sh
% 0.84/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.05  % done 763 iterations in 0.573s
% 0.84/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.05  % SZS output start Refutation
% 0.84/1.05  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.84/1.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.05  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.84/1.05  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.84/1.05  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.84/1.05  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.84/1.05  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.84/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.05  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.84/1.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.84/1.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.84/1.05  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.84/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.05  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.84/1.05  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.84/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.05  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.84/1.05  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.84/1.05  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.84/1.05  thf(t56_tex_2, conjecture,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.84/1.05         ( l1_pre_topc @ A ) ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.05           ( ![C:$i]:
% 0.84/1.05             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.05               ( ( r1_xboole_0 @
% 0.84/1.05                   ( k2_pre_topc @
% 0.84/1.05                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.84/1.05                   ( k2_pre_topc @
% 0.84/1.05                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.84/1.05                 ( ( k2_pre_topc @
% 0.84/1.05                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.84/1.05                   ( k2_pre_topc @
% 0.84/1.05                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.05    (~( ![A:$i]:
% 0.84/1.05        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.84/1.05            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.05          ( ![B:$i]:
% 0.84/1.05            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.05              ( ![C:$i]:
% 0.84/1.05                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.05                  ( ( r1_xboole_0 @
% 0.84/1.05                      ( k2_pre_topc @
% 0.84/1.05                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.84/1.05                      ( k2_pre_topc @
% 0.84/1.05                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.84/1.05                    ( ( k2_pre_topc @
% 0.84/1.05                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.84/1.05                      ( k2_pre_topc @
% 0.84/1.05                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.84/1.05    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.84/1.05  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(redefinition_k6_domain_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.84/1.05       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.84/1.05  thf('2', plain,
% 0.84/1.05      (![X17 : $i, X18 : $i]:
% 0.84/1.05         ((v1_xboole_0 @ X17)
% 0.84/1.05          | ~ (m1_subset_1 @ X18 @ X17)
% 0.84/1.05          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.84/1.05  thf('3', plain,
% 0.84/1.05      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.05  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(dt_k6_domain_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.84/1.05       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.84/1.05  thf('5', plain,
% 0.84/1.05      (![X15 : $i, X16 : $i]:
% 0.84/1.05         ((v1_xboole_0 @ X15)
% 0.84/1.05          | ~ (m1_subset_1 @ X16 @ X15)
% 0.84/1.05          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.84/1.05  thf('6', plain,
% 0.84/1.05      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.84/1.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['4', '5'])).
% 0.84/1.05  thf('7', plain,
% 0.84/1.05      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.84/1.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['3', '6'])).
% 0.84/1.05  thf('8', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['7'])).
% 0.84/1.05  thf(l27_zfmisc_1, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.84/1.05  thf('9', plain,
% 0.84/1.05      (![X5 : $i, X6 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ (k1_tarski @ X5) @ X6) | (r2_hidden @ X5 @ X6))),
% 0.84/1.05      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.84/1.05  thf(t3_xboole_0, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.84/1.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.84/1.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.84/1.05            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.84/1.05  thf('10', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.84/1.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.05  thf('11', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.84/1.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.05  thf('12', plain,
% 0.84/1.05      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X2 @ X0)
% 0.84/1.05          | ~ (r2_hidden @ X2 @ X3)
% 0.84/1.05          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.84/1.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.84/1.05  thf('13', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X1 @ X0)
% 0.84/1.05          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.84/1.05          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.84/1.05      inference('sup-', [status(thm)], ['11', '12'])).
% 0.84/1.05  thf('14', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((r1_xboole_0 @ X0 @ X1)
% 0.84/1.05          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.84/1.05          | (r1_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('sup-', [status(thm)], ['10', '13'])).
% 0.84/1.05  thf('15', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.84/1.05      inference('simplify', [status(thm)], ['14'])).
% 0.84/1.05  thf('16', plain,
% 0.84/1.05      (![X0 : $i, X1 : $i]:
% 0.84/1.05         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['9', '15'])).
% 0.84/1.05  thf('17', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('18', plain,
% 0.84/1.05      (![X17 : $i, X18 : $i]:
% 0.84/1.05         ((v1_xboole_0 @ X17)
% 0.84/1.05          | ~ (m1_subset_1 @ X18 @ X17)
% 0.84/1.05          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.84/1.05      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.84/1.05  thf('19', plain,
% 0.84/1.05      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.05  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('21', plain,
% 0.84/1.05      (![X15 : $i, X16 : $i]:
% 0.84/1.05         ((v1_xboole_0 @ X15)
% 0.84/1.05          | ~ (m1_subset_1 @ X16 @ X15)
% 0.84/1.05          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.84/1.05  thf('22', plain,
% 0.84/1.05      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.84/1.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['20', '21'])).
% 0.84/1.05  thf('23', plain,
% 0.84/1.05      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.84/1.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup+', [status(thm)], ['19', '22'])).
% 0.84/1.05  thf('24', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['23'])).
% 0.84/1.05  thf(dt_k2_pre_topc, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( l1_pre_topc @ A ) & 
% 0.84/1.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.05       ( m1_subset_1 @
% 0.84/1.05         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.84/1.05  thf('25', plain,
% 0.84/1.05      (![X7 : $i, X8 : $i]:
% 0.84/1.05         (~ (l1_pre_topc @ X7)
% 0.84/1.05          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.84/1.05          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.84/1.05             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.84/1.05  thf('26', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['24', '25'])).
% 0.84/1.05  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('28', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.05  thf(t52_pre_topc, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( l1_pre_topc @ A ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.05           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.84/1.05             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.84/1.05               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.84/1.05  thf('29', plain,
% 0.84/1.05      (![X13 : $i, X14 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.84/1.05          | ~ (v2_pre_topc @ X14)
% 0.84/1.05          | ((k2_pre_topc @ X14 @ X13) != (X13))
% 0.84/1.05          | (v4_pre_topc @ X13 @ X14)
% 0.84/1.05          | ~ (l1_pre_topc @ X14))),
% 0.84/1.05      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.84/1.05  thf('30', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.05        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.84/1.05        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05            != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05        | ~ (v2_pre_topc @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['28', '29'])).
% 0.84/1.05  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('33', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.84/1.05        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05            != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.84/1.05      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.84/1.05  thf('34', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['23'])).
% 0.84/1.05  thf(projectivity_k2_pre_topc, axiom,
% 0.84/1.05    (![A:$i,B:$i]:
% 0.84/1.05     ( ( ( l1_pre_topc @ A ) & 
% 0.84/1.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.84/1.05       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.84/1.05         ( k2_pre_topc @ A @ B ) ) ))).
% 0.84/1.05  thf('35', plain,
% 0.84/1.05      (![X11 : $i, X12 : $i]:
% 0.84/1.05         (~ (l1_pre_topc @ X11)
% 0.84/1.05          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.84/1.05          | ((k2_pre_topc @ X11 @ (k2_pre_topc @ X11 @ X12))
% 0.84/1.05              = (k2_pre_topc @ X11 @ X12)))),
% 0.84/1.05      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.84/1.05  thf('36', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['34', '35'])).
% 0.84/1.05  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('38', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.84/1.05      inference('demod', [status(thm)], ['36', '37'])).
% 0.84/1.05  thf('39', plain,
% 0.84/1.05      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('clc', [status(thm)], ['33', '38'])).
% 0.84/1.05  thf('40', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.05  thf(t24_tdlat_3, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.05       ( ( v3_tdlat_3 @ A ) <=>
% 0.84/1.05         ( ![B:$i]:
% 0.84/1.05           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.05             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.84/1.05  thf('41', plain,
% 0.84/1.05      (![X19 : $i, X20 : $i]:
% 0.84/1.05         (~ (v3_tdlat_3 @ X19)
% 0.84/1.05          | ~ (v4_pre_topc @ X20 @ X19)
% 0.84/1.05          | (v3_pre_topc @ X20 @ X19)
% 0.84/1.05          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.84/1.05          | ~ (l1_pre_topc @ X19)
% 0.84/1.05          | ~ (v2_pre_topc @ X19))),
% 0.84/1.05      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.84/1.05  thf('42', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ~ (v2_pre_topc @ sk_A)
% 0.84/1.05        | ~ (l1_pre_topc @ sk_A)
% 0.84/1.05        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.84/1.05        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.84/1.05        | ~ (v3_tdlat_3 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['40', '41'])).
% 0.84/1.05  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('45', plain, ((v3_tdlat_3 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('46', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.84/1.05        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.84/1.05  thf('47', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['39', '46'])).
% 0.84/1.05  thf('48', plain,
% 0.84/1.05      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['47'])).
% 0.84/1.05  thf('49', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.05      inference('demod', [status(thm)], ['26', '27'])).
% 0.84/1.05  thf(t40_tsep_1, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.05           ( ![C:$i]:
% 0.84/1.05             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.05               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.84/1.05                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf('50', plain,
% 0.84/1.05      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.84/1.05          | ~ (v3_pre_topc @ X21 @ X22)
% 0.84/1.05          | ~ (r1_xboole_0 @ X21 @ X23)
% 0.84/1.05          | (r1_xboole_0 @ X21 @ (k2_pre_topc @ X22 @ X23))
% 0.84/1.05          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.84/1.05          | ~ (l1_pre_topc @ X22)
% 0.84/1.05          | ~ (v2_pre_topc @ X22))),
% 0.84/1.05      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.84/1.05  thf('51', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05          | ~ (v2_pre_topc @ sk_A)
% 0.84/1.05          | ~ (l1_pre_topc @ sk_A)
% 0.84/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.84/1.05          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.84/1.05          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['49', '50'])).
% 0.84/1.05  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('54', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.84/1.05          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.84/1.05          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.84/1.05      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.84/1.05  thf('55', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.84/1.05          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.84/1.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['48', '54'])).
% 0.84/1.05  thf('56', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.05          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05             (k2_pre_topc @ sk_A @ X0))
% 0.84/1.05          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.84/1.05          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['55'])).
% 0.84/1.05  thf('57', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.84/1.05          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.84/1.05               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['16', '56'])).
% 0.84/1.05  thf('58', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (r2_hidden @ sk_C_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.84/1.05      inference('sup-', [status(thm)], ['8', '57'])).
% 0.84/1.05  thf('59', plain,
% 0.84/1.05      (((r2_hidden @ sk_C_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['58'])).
% 0.84/1.05  thf('60', plain,
% 0.84/1.05      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.05  thf('61', plain,
% 0.84/1.05      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.05  thf('62', plain,
% 0.84/1.05      (~ (r1_xboole_0 @ 
% 0.84/1.05          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.84/1.05          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('63', plain,
% 0.84/1.05      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['61', '62'])).
% 0.84/1.05  thf('64', plain,
% 0.84/1.05      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['60', '63'])).
% 0.84/1.05  thf('65', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.84/1.05             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_1))))),
% 0.84/1.05      inference('simplify', [status(thm)], ['64'])).
% 0.84/1.05  thf('66', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | (r2_hidden @ sk_C_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.84/1.05      inference('clc', [status(thm)], ['59', '65'])).
% 0.84/1.05  thf('67', plain,
% 0.84/1.05      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['17', '18'])).
% 0.84/1.05  thf(t55_tex_2, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.84/1.05         ( l1_pre_topc @ A ) ) =>
% 0.84/1.05       ( ![B:$i]:
% 0.84/1.05         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.05           ( ![C:$i]:
% 0.84/1.05             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.05               ( ( r2_hidden @
% 0.84/1.05                   B @ 
% 0.84/1.05                   ( k2_pre_topc @
% 0.84/1.05                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.84/1.05                 ( ( k2_pre_topc @
% 0.84/1.05                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.84/1.05                   ( k2_pre_topc @
% 0.84/1.05                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.84/1.05  thf('68', plain,
% 0.84/1.05      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.84/1.05         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.84/1.05          | ~ (r2_hidden @ X24 @ 
% 0.84/1.05               (k2_pre_topc @ X25 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X26)))
% 0.84/1.05          | ((k2_pre_topc @ X25 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24))
% 0.84/1.05              = (k2_pre_topc @ X25 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X26)))
% 0.84/1.05          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.84/1.05          | ~ (l1_pre_topc @ X25)
% 0.84/1.05          | ~ (v3_tdlat_3 @ X25)
% 0.84/1.05          | ~ (v2_pre_topc @ X25)
% 0.84/1.05          | (v2_struct_0 @ X25))),
% 0.84/1.05      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.84/1.05  thf('69', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05          | (v2_struct_0 @ sk_A)
% 0.84/1.05          | ~ (v2_pre_topc @ sk_A)
% 0.84/1.05          | ~ (v3_tdlat_3 @ sk_A)
% 0.84/1.05          | ~ (l1_pre_topc @ sk_A)
% 0.84/1.05          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.84/1.05          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.84/1.05              = (k2_pre_topc @ sk_A @ 
% 0.84/1.05                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.84/1.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['67', '68'])).
% 0.84/1.05  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('71', plain, ((v3_tdlat_3 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('73', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('74', plain,
% 0.84/1.05      (![X0 : $i]:
% 0.84/1.05         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.84/1.05          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05          | (v2_struct_0 @ sk_A)
% 0.84/1.05          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.84/1.05              = (k2_pre_topc @ sk_A @ 
% 0.84/1.05                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.84/1.05          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.84/1.05  thf('75', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.84/1.05            = (k2_pre_topc @ sk_A @ 
% 0.84/1.05               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.84/1.05        | (v2_struct_0 @ sk_A)
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('sup-', [status(thm)], ['66', '74'])).
% 0.84/1.05  thf('76', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('77', plain,
% 0.84/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.84/1.05        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.84/1.05            = (k2_pre_topc @ sk_A @ 
% 0.84/1.05               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.84/1.05        | (v2_struct_0 @ sk_A)
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('demod', [status(thm)], ['75', '76'])).
% 0.84/1.05  thf('78', plain,
% 0.84/1.05      (((v2_struct_0 @ sk_A)
% 0.84/1.05        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.84/1.05            = (k2_pre_topc @ sk_A @ 
% 0.84/1.05               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.84/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('simplify', [status(thm)], ['77'])).
% 0.84/1.05  thf('79', plain,
% 0.84/1.05      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.84/1.05         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('80', plain,
% 0.84/1.05      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.05      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.84/1.05  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf('82', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.84/1.05      inference('clc', [status(thm)], ['80', '81'])).
% 0.84/1.05  thf(fc2_struct_0, axiom,
% 0.84/1.05    (![A:$i]:
% 0.84/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.84/1.05       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.84/1.05  thf('83', plain,
% 0.84/1.05      (![X10 : $i]:
% 0.84/1.05         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.84/1.05          | ~ (l1_struct_0 @ X10)
% 0.84/1.05          | (v2_struct_0 @ X10))),
% 0.84/1.05      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.84/1.05  thf('84', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.84/1.05      inference('sup-', [status(thm)], ['82', '83'])).
% 0.84/1.05  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.05  thf(dt_l1_pre_topc, axiom,
% 0.84/1.05    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.84/1.05  thf('86', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.84/1.05      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.84/1.05  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.84/1.05      inference('sup-', [status(thm)], ['85', '86'])).
% 0.84/1.05  thf('88', plain, ((v2_struct_0 @ sk_A)),
% 0.84/1.05      inference('demod', [status(thm)], ['84', '87'])).
% 0.84/1.05  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 0.84/1.05  
% 0.84/1.05  % SZS output end Refutation
% 0.84/1.05  
% 0.84/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
