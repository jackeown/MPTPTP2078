%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VVcvfQhPr7

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:30 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 232 expanded)
%              Number of leaves         :   32 (  78 expanded)
%              Depth                    :   26
%              Number of atoms          : 1221 (4452 expanded)
%              Number of equality atoms :   27 ( 109 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_pre_topc @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
       != X11 )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_pre_topc @ X9 @ ( k2_pre_topc @ X9 @ X10 ) )
        = ( k2_pre_topc @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v4_pre_topc @ X18 @ X17 )
      | ( v3_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_xboole_0 @ X19 @ ( k2_pre_topc @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('56',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('57',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['54','60'])).

thf('62',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('63',plain,(
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

thf('64',plain,(
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
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['75','76'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('78',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('81',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VVcvfQhPr7
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:28:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 653 iterations in 0.422s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.87  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.68/0.87  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.68/0.87  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.87  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.68/0.87  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.68/0.87  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.68/0.87  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.68/0.87  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.87  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.68/0.87  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.68/0.87  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.87  thf(t56_tex_2, conjecture,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.68/0.87         ( l1_pre_topc @ A ) ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87           ( ![C:$i]:
% 0.68/0.87             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87               ( ( r1_xboole_0 @
% 0.68/0.87                   ( k2_pre_topc @
% 0.68/0.87                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.68/0.87                   ( k2_pre_topc @
% 0.68/0.87                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.68/0.87                 ( ( k2_pre_topc @
% 0.68/0.87                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.68/0.87                   ( k2_pre_topc @
% 0.68/0.87                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i]:
% 0.68/0.87        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.68/0.87            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.87          ( ![B:$i]:
% 0.68/0.87            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87              ( ![C:$i]:
% 0.68/0.87                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.87                  ( ( r1_xboole_0 @
% 0.68/0.87                      ( k2_pre_topc @
% 0.68/0.87                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.68/0.87                      ( k2_pre_topc @
% 0.68/0.87                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.68/0.87                    ( ( k2_pre_topc @
% 0.68/0.87                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.68/0.87                      ( k2_pre_topc @
% 0.68/0.87                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.68/0.87  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(redefinition_k6_domain_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.68/0.87       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (![X15 : $i, X16 : $i]:
% 0.68/0.87         ((v1_xboole_0 @ X15)
% 0.68/0.87          | ~ (m1_subset_1 @ X16 @ X15)
% 0.68/0.87          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.68/0.87  thf('3', plain,
% 0.68/0.87      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.87  thf('4', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(dt_k6_domain_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.68/0.87       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      (![X13 : $i, X14 : $i]:
% 0.68/0.87         ((v1_xboole_0 @ X13)
% 0.68/0.87          | ~ (m1_subset_1 @ X14 @ X13)
% 0.68/0.87          | (m1_subset_1 @ (k6_domain_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13)))),
% 0.68/0.87      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.68/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.68/0.87  thf('7', plain,
% 0.68/0.87      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.68/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['3', '6'])).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.68/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.87      inference('simplify', [status(thm)], ['7'])).
% 0.68/0.87  thf(l27_zfmisc_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.68/0.87  thf('9', plain,
% 0.68/0.87      (![X3 : $i, X4 : $i]:
% 0.68/0.87         ((r1_xboole_0 @ (k1_tarski @ X3) @ X4) | (r2_hidden @ X3 @ X4))),
% 0.68/0.87      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.68/0.87  thf(symmetry_r1_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.68/0.87  thf('10', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.68/0.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.68/0.87  thf('11', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.87  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      (![X15 : $i, X16 : $i]:
% 0.68/0.87         ((v1_xboole_0 @ X15)
% 0.68/0.87          | ~ (m1_subset_1 @ X16 @ X15)
% 0.68/0.87          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.68/0.87      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.68/0.87  thf('14', plain,
% 0.68/0.87      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (![X13 : $i, X14 : $i]:
% 0.68/0.87         ((v1_xboole_0 @ X13)
% 0.68/0.87          | ~ (m1_subset_1 @ X14 @ X13)
% 0.68/0.87          | (m1_subset_1 @ (k6_domain_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13)))),
% 0.68/0.87      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.68/0.87  thf('17', plain,
% 0.68/0.87      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.68/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.87  thf('18', plain,
% 0.68/0.87      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.68/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['14', '17'])).
% 0.68/0.87  thf('19', plain,
% 0.68/0.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.68/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.87      inference('simplify', [status(thm)], ['18'])).
% 0.68/0.87  thf(dt_k2_pre_topc, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( l1_pre_topc @ A ) & 
% 0.68/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.87       ( m1_subset_1 @
% 0.68/0.87         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.68/0.87  thf('20', plain,
% 0.68/0.87      (![X5 : $i, X6 : $i]:
% 0.68/0.87         (~ (l1_pre_topc @ X5)
% 0.68/0.87          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.68/0.87          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.68/0.87             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.68/0.87      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.68/0.87  thf('21', plain,
% 0.68/0.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.87  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('23', plain,
% 0.68/0.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.87      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.87  thf(t52_pre_topc, axiom,
% 0.68/0.87    (![A:$i]:
% 0.68/0.87     ( ( l1_pre_topc @ A ) =>
% 0.68/0.87       ( ![B:$i]:
% 0.68/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.87           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.68/0.87             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.68/0.87               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.68/0.87  thf('24', plain,
% 0.68/0.87      (![X11 : $i, X12 : $i]:
% 0.68/0.87         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.68/0.87          | ~ (v2_pre_topc @ X12)
% 0.68/0.87          | ((k2_pre_topc @ X12 @ X11) != (X11))
% 0.68/0.87          | (v4_pre_topc @ X11 @ X12)
% 0.68/0.87          | ~ (l1_pre_topc @ X12))),
% 0.68/0.87      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.68/0.87  thf('25', plain,
% 0.68/0.87      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.87        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.87        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88            != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88        | ~ (v2_pre_topc @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['23', '24'])).
% 0.68/0.88  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88            != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.68/0.88      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.68/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['18'])).
% 0.68/0.88  thf(projectivity_k2_pre_topc, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( l1_pre_topc @ A ) & 
% 0.68/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.68/0.88         ( k2_pre_topc @ A @ B ) ) ))).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X9 : $i, X10 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X9)
% 0.68/0.88          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.68/0.88          | ((k2_pre_topc @ X9 @ (k2_pre_topc @ X9 @ X10))
% 0.68/0.88              = (k2_pre_topc @ X9 @ X10)))),
% 0.68/0.88      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.88  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.68/0.88      inference('demod', [status(thm)], ['31', '32'])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('clc', [status(thm)], ['28', '33'])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf(t24_tdlat_3, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.88       ( ( v3_tdlat_3 @ A ) <=>
% 0.68/0.88         ( ![B:$i]:
% 0.68/0.88           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.68/0.88  thf('36', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i]:
% 0.68/0.88         (~ (v3_tdlat_3 @ X17)
% 0.68/0.88          | ~ (v4_pre_topc @ X18 @ X17)
% 0.68/0.88          | (v3_pre_topc @ X18 @ X17)
% 0.68/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.68/0.88          | ~ (l1_pre_topc @ X17)
% 0.68/0.88          | ~ (v2_pre_topc @ X17))),
% 0.68/0.88      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.68/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.68/0.88        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.88        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.88        | ~ (v3_tdlat_3 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['35', '36'])).
% 0.68/0.88  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('40', plain, ((v3_tdlat_3 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.88        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['34', '41'])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf(t40_tsep_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88           ( ![C:$i]:
% 0.68/0.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.68/0.88                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.68/0.88          | ~ (v3_pre_topc @ X19 @ X20)
% 0.68/0.88          | ~ (r1_xboole_0 @ X19 @ X21)
% 0.68/0.88          | (r1_xboole_0 @ X19 @ (k2_pre_topc @ X20 @ X21))
% 0.68/0.88          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.68/0.88          | ~ (l1_pre_topc @ X20)
% 0.68/0.88          | ~ (v2_pre_topc @ X20))),
% 0.68/0.88      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | ~ (v2_pre_topc @ sk_A)
% 0.68/0.88          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ X0))
% 0.68/0.88          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.68/0.88          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['44', '45'])).
% 0.68/0.88  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ X0))
% 0.68/0.88          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.68/0.88          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.68/0.88          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ X0))
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['43', '49'])).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.68/0.88          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ X0))
% 0.68/0.88          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.68/0.88          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['50'])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.68/0.88          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.68/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['11', '51'])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['8', '52'])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['53'])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      (~ (r1_xboole_0 @ 
% 0.68/0.88          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.68/0.88          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['56', '57'])).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['55', '58'])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.68/0.88             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['59'])).
% 0.68/0.88  thf('61', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.68/0.88      inference('clc', [status(thm)], ['54', '60'])).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.88  thf(t55_tex_2, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.68/0.88         ( l1_pre_topc @ A ) ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88           ( ![C:$i]:
% 0.68/0.88             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.68/0.88               ( ( r2_hidden @
% 0.68/0.88                   B @ 
% 0.68/0.88                   ( k2_pre_topc @
% 0.68/0.88                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.68/0.88                 ( ( k2_pre_topc @
% 0.68/0.88                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.68/0.88                   ( k2_pre_topc @
% 0.68/0.88                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.68/0.88          | ~ (r2_hidden @ X22 @ 
% 0.68/0.88               (k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X24)))
% 0.68/0.88          | ((k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X22))
% 0.68/0.88              = (k2_pre_topc @ X23 @ (k6_domain_1 @ (u1_struct_0 @ X23) @ X24)))
% 0.68/0.88          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.68/0.88          | ~ (l1_pre_topc @ X23)
% 0.68/0.88          | ~ (v3_tdlat_3 @ X23)
% 0.68/0.88          | ~ (v2_pre_topc @ X23)
% 0.68/0.88          | (v2_struct_0 @ X23))),
% 0.68/0.88      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.68/0.88  thf('64', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | (v2_struct_0 @ sk_A)
% 0.68/0.88          | ~ (v2_pre_topc @ sk_A)
% 0.68/0.88          | ~ (v3_tdlat_3 @ sk_A)
% 0.68/0.88          | ~ (l1_pre_topc @ sk_A)
% 0.68/0.88          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.68/0.88              = (k2_pre_topc @ sk_A @ 
% 0.68/0.88                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['62', '63'])).
% 0.68/0.88  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('66', plain, ((v3_tdlat_3 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('68', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.68/0.88          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88          | (v2_struct_0 @ sk_A)
% 0.68/0.88          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.68/0.88              = (k2_pre_topc @ sk_A @ 
% 0.68/0.88                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.68/0.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.68/0.88            = (k2_pre_topc @ sk_A @ 
% 0.68/0.88               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.68/0.88        | (v2_struct_0 @ sk_A)
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['61', '69'])).
% 0.68/0.88  thf('71', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('72', plain,
% 0.68/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.68/0.88            = (k2_pre_topc @ sk_A @ 
% 0.68/0.88               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.68/0.88        | (v2_struct_0 @ sk_A)
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('demod', [status(thm)], ['70', '71'])).
% 0.68/0.88  thf('73', plain,
% 0.68/0.88      (((v2_struct_0 @ sk_A)
% 0.68/0.88        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.68/0.88            = (k2_pre_topc @ sk_A @ 
% 0.68/0.88               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.68/0.88        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['72'])).
% 0.68/0.88  thf('74', plain,
% 0.68/0.88      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.68/0.88         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.68/0.88  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('77', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.68/0.88      inference('clc', [status(thm)], ['75', '76'])).
% 0.68/0.88  thf(fc2_struct_0, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.68/0.88       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.68/0.88  thf('78', plain,
% 0.68/0.88      (![X8 : $i]:
% 0.68/0.88         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.68/0.88          | ~ (l1_struct_0 @ X8)
% 0.68/0.88          | (v2_struct_0 @ X8))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.68/0.88  thf('79', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['77', '78'])).
% 0.68/0.88  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(dt_l1_pre_topc, axiom,
% 0.68/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.68/0.88  thf('81', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.88  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.68/0.88      inference('sup-', [status(thm)], ['80', '81'])).
% 0.68/0.88  thf('83', plain, ((v2_struct_0 @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['79', '82'])).
% 0.68/0.88  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
