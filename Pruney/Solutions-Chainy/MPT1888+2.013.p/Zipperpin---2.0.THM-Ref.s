%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VnPdHOLut4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:29 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 202 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   24
%              Number of atoms          : 1089 (3847 expanded)
%              Number of equality atoms :   18 (  89 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_tdlat_3 @ X15 )
      | ~ ( v4_pre_topc @ X16 @ X15 )
      | ( v3_pre_topc @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','35'])).

thf('37',plain,
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

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 )
      | ( r1_xboole_0 @ X17 @ ( k2_pre_topc @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_tsep_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
    | ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('49',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('50',plain,(
    ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['47','53'])).

thf('55',plain,
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

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k2_pre_topc @ X21 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X22 ) ) )
      | ( ( k2_pre_topc @ X21 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) )
        = ( k2_pre_topc @ X21 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v3_tdlat_3 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_tex_2])).

thf('57',plain,(
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
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('71',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('74',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VnPdHOLut4
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.67  % Solved by: fo/fo7.sh
% 0.51/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.67  % done 329 iterations in 0.225s
% 0.51/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.67  % SZS output start Refutation
% 0.51/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.51/0.67  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.51/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.67  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.51/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.51/0.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.51/0.67  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.51/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.67  thf(t56_tex_2, conjecture,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.51/0.67         ( l1_pre_topc @ A ) ) =>
% 0.51/0.67       ( ![B:$i]:
% 0.51/0.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.67           ( ![C:$i]:
% 0.51/0.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.67               ( ( r1_xboole_0 @
% 0.51/0.67                   ( k2_pre_topc @
% 0.51/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.51/0.67                   ( k2_pre_topc @
% 0.51/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.51/0.67                 ( ( k2_pre_topc @
% 0.51/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.51/0.67                   ( k2_pre_topc @
% 0.51/0.67                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.51/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.67    (~( ![A:$i]:
% 0.51/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.51/0.67            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.67          ( ![B:$i]:
% 0.51/0.67            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.67              ( ![C:$i]:
% 0.51/0.67                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.67                  ( ( r1_xboole_0 @
% 0.51/0.67                      ( k2_pre_topc @
% 0.51/0.67                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) @ 
% 0.51/0.67                      ( k2_pre_topc @
% 0.51/0.67                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) | 
% 0.51/0.67                    ( ( k2_pre_topc @
% 0.51/0.67                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.51/0.67                      ( k2_pre_topc @
% 0.51/0.67                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.51/0.67    inference('cnf.neg', [status(esa)], [t56_tex_2])).
% 0.51/0.67  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf(redefinition_k6_domain_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.51/0.67       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.51/0.67  thf('2', plain,
% 0.51/0.67      (![X11 : $i, X12 : $i]:
% 0.51/0.67         ((v1_xboole_0 @ X11)
% 0.51/0.67          | ~ (m1_subset_1 @ X12 @ X11)
% 0.51/0.67          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.51/0.67      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.51/0.67  thf('3', plain,
% 0.51/0.67      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.67  thf('4', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf(dt_k6_domain_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.51/0.67       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.67  thf('5', plain,
% 0.51/0.67      (![X9 : $i, X10 : $i]:
% 0.51/0.67         ((v1_xboole_0 @ X9)
% 0.51/0.67          | ~ (m1_subset_1 @ X10 @ X9)
% 0.51/0.67          | (m1_subset_1 @ (k6_domain_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.51/0.67      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.51/0.67  thf('6', plain,
% 0.51/0.67      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.51/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.67  thf('7', plain,
% 0.51/0.67      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.51/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('sup+', [status(thm)], ['3', '6'])).
% 0.51/0.67  thf('8', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.51/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['7'])).
% 0.51/0.67  thf(l27_zfmisc_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.51/0.67  thf('9', plain,
% 0.51/0.67      (![X3 : $i, X4 : $i]:
% 0.51/0.67         ((r1_xboole_0 @ (k1_tarski @ X3) @ X4) | (r2_hidden @ X3 @ X4))),
% 0.51/0.67      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.51/0.67  thf(symmetry_r1_xboole_0, axiom,
% 0.51/0.67    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.51/0.67  thf('10', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.51/0.67      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.51/0.67  thf('11', plain,
% 0.51/0.67      (![X0 : $i, X1 : $i]:
% 0.51/0.67         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.67  thf('12', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('13', plain,
% 0.51/0.67      (![X11 : $i, X12 : $i]:
% 0.51/0.67         ((v1_xboole_0 @ X11)
% 0.51/0.67          | ~ (m1_subset_1 @ X12 @ X11)
% 0.51/0.67          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.51/0.67      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.51/0.67  thf('14', plain,
% 0.51/0.67      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.67  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('16', plain,
% 0.51/0.67      (![X9 : $i, X10 : $i]:
% 0.51/0.67         ((v1_xboole_0 @ X9)
% 0.51/0.67          | ~ (m1_subset_1 @ X10 @ X9)
% 0.51/0.67          | (m1_subset_1 @ (k6_domain_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.51/0.67      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.51/0.67  thf('17', plain,
% 0.51/0.67      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.51/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['15', '16'])).
% 0.51/0.67  thf('18', plain,
% 0.51/0.67      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.51/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('sup+', [status(thm)], ['14', '17'])).
% 0.51/0.67  thf('19', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.51/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['18'])).
% 0.51/0.67  thf(dt_k2_pre_topc, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( l1_pre_topc @ A ) & 
% 0.51/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.67       ( m1_subset_1 @
% 0.51/0.67         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.67  thf('20', plain,
% 0.51/0.67      (![X5 : $i, X6 : $i]:
% 0.51/0.67         (~ (l1_pre_topc @ X5)
% 0.51/0.67          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.51/0.67          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.51/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.51/0.67      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.51/0.67  thf('21', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.51/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.67  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('23', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.67      inference('demod', [status(thm)], ['21', '22'])).
% 0.51/0.67  thf(t24_tdlat_3, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.67       ( ( v3_tdlat_3 @ A ) <=>
% 0.51/0.67         ( ![B:$i]:
% 0.51/0.67           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.67             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.51/0.67  thf('24', plain,
% 0.51/0.67      (![X15 : $i, X16 : $i]:
% 0.51/0.67         (~ (v3_tdlat_3 @ X15)
% 0.51/0.67          | ~ (v4_pre_topc @ X16 @ X15)
% 0.51/0.67          | (v3_pre_topc @ X16 @ X15)
% 0.51/0.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.51/0.67          | ~ (l1_pre_topc @ X15)
% 0.51/0.67          | ~ (v2_pre_topc @ X15))),
% 0.51/0.67      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 0.51/0.67  thf('25', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.67        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.67        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.51/0.67        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.51/0.67        | ~ (v3_tdlat_3 @ sk_A))),
% 0.51/0.67      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.67  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('28', plain, ((v3_tdlat_3 @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('29', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.51/0.67        | ~ (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.51/0.67      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.51/0.67  thf('30', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.51/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.67      inference('simplify', [status(thm)], ['18'])).
% 0.51/0.67  thf(fc1_tops_1, axiom,
% 0.51/0.67    (![A:$i,B:$i]:
% 0.51/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.51/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.67       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.51/0.67  thf('31', plain,
% 0.51/0.67      (![X13 : $i, X14 : $i]:
% 0.51/0.67         (~ (l1_pre_topc @ X13)
% 0.51/0.67          | ~ (v2_pre_topc @ X13)
% 0.51/0.67          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.51/0.67          | (v4_pre_topc @ (k2_pre_topc @ X13 @ X14) @ X13))),
% 0.51/0.67      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.51/0.67  thf('32', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.51/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.51/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.51/0.67      inference('sup-', [status(thm)], ['30', '31'])).
% 0.51/0.67  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('35', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.51/0.67      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.51/0.67  thf('36', plain,
% 0.51/0.67      (((v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A)
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('clc', [status(thm)], ['29', '35'])).
% 0.51/0.67  thf('37', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.67      inference('demod', [status(thm)], ['21', '22'])).
% 0.51/0.67  thf(t40_tsep_1, axiom,
% 0.51/0.67    (![A:$i]:
% 0.51/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.67       ( ![B:$i]:
% 0.51/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.67           ( ![C:$i]:
% 0.51/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.67               ( ( ( r1_xboole_0 @ B @ C ) & ( v3_pre_topc @ B @ A ) ) =>
% 0.51/0.67                 ( r1_xboole_0 @ B @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.51/0.67  thf('38', plain,
% 0.51/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.67         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.51/0.67          | ~ (v3_pre_topc @ X17 @ X18)
% 0.51/0.67          | ~ (r1_xboole_0 @ X17 @ X19)
% 0.51/0.67          | (r1_xboole_0 @ X17 @ (k2_pre_topc @ X18 @ X19))
% 0.51/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.51/0.67          | ~ (l1_pre_topc @ X18)
% 0.51/0.67          | ~ (v2_pre_topc @ X18))),
% 0.51/0.67      inference('cnf', [status(esa)], [t40_tsep_1])).
% 0.51/0.67  thf('39', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.67          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67             (k2_pre_topc @ sk_A @ X0))
% 0.51/0.67          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.51/0.67          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.51/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.51/0.67  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.67  thf('42', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67             (k2_pre_topc @ sk_A @ X0))
% 0.51/0.67          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.51/0.67          | ~ (v3_pre_topc @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ sk_A))),
% 0.51/0.67      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.51/0.67  thf('43', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.51/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67             (k2_pre_topc @ sk_A @ X0))
% 0.51/0.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('sup-', [status(thm)], ['36', '42'])).
% 0.51/0.67  thf('44', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67             (k2_pre_topc @ sk_A @ X0))
% 0.51/0.67          | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ X0)
% 0.51/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.67      inference('simplify', [status(thm)], ['43'])).
% 0.51/0.67  thf('45', plain,
% 0.51/0.67      (![X0 : $i]:
% 0.51/0.67         ((r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.51/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67          | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67             (k2_pre_topc @ sk_A @ (k1_tarski @ X0)))
% 0.51/0.67          | ~ (m1_subset_1 @ (k1_tarski @ X0) @ 
% 0.51/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['11', '44'])).
% 0.51/0.67  thf('46', plain,
% 0.51/0.67      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.67           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.51/0.67        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.67        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.51/0.67      inference('sup-', [status(thm)], ['8', '45'])).
% 0.51/0.68  thf('47', plain,
% 0.51/0.68      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.51/0.68        | (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.68           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['46'])).
% 0.51/0.68  thf('48', plain,
% 0.51/0.68      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.68  thf('49', plain,
% 0.51/0.68      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf('50', plain,
% 0.51/0.68      (~ (r1_xboole_0 @ 
% 0.51/0.68          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.51/0.68          (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('51', plain,
% 0.51/0.68      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.68           (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['49', '50'])).
% 0.51/0.68  thf('52', plain,
% 0.51/0.68      ((~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.68           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C)))
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['48', '51'])).
% 0.51/0.68  thf('53', plain,
% 0.51/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.68        | ~ (r1_xboole_0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.51/0.68             (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['52'])).
% 0.51/0.68  thf('54', plain,
% 0.51/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.68        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.51/0.68      inference('clc', [status(thm)], ['47', '53'])).
% 0.51/0.68  thf('55', plain,
% 0.51/0.68      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.68  thf(t55_tex_2, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.51/0.68         ( l1_pre_topc @ A ) ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.68           ( ![C:$i]:
% 0.51/0.68             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.68               ( ( r2_hidden @
% 0.51/0.68                   B @ 
% 0.51/0.68                   ( k2_pre_topc @
% 0.51/0.68                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =>
% 0.51/0.68                 ( ( k2_pre_topc @
% 0.51/0.68                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.51/0.68                   ( k2_pre_topc @
% 0.51/0.68                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.51/0.68  thf('56', plain,
% 0.51/0.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.68         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.51/0.68          | ~ (r2_hidden @ X20 @ 
% 0.51/0.68               (k2_pre_topc @ X21 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X22)))
% 0.51/0.68          | ((k2_pre_topc @ X21 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20))
% 0.51/0.68              = (k2_pre_topc @ X21 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X22)))
% 0.51/0.68          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.51/0.68          | ~ (l1_pre_topc @ X21)
% 0.51/0.68          | ~ (v3_tdlat_3 @ X21)
% 0.51/0.68          | ~ (v2_pre_topc @ X21)
% 0.51/0.68          | (v2_struct_0 @ X21))),
% 0.51/0.68      inference('cnf', [status(esa)], [t55_tex_2])).
% 0.51/0.68  thf('57', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.51/0.68          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.68          | (v2_struct_0 @ sk_A)
% 0.51/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.51/0.68          | ~ (v3_tdlat_3 @ sk_A)
% 0.51/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.68          | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.51/0.68          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.51/0.68              = (k2_pre_topc @ sk_A @ 
% 0.51/0.68                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.51/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.51/0.68  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('59', plain, ((v3_tdlat_3 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('61', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('62', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.51/0.68          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.68          | (v2_struct_0 @ sk_A)
% 0.51/0.68          | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.51/0.68              = (k2_pre_topc @ sk_A @ 
% 0.51/0.68                 (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.51/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.51/0.68  thf('63', plain,
% 0.51/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.68        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.51/0.68        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.51/0.68            = (k2_pre_topc @ sk_A @ 
% 0.51/0.68               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.51/0.68        | (v2_struct_0 @ sk_A)
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['54', '62'])).
% 0.51/0.68  thf('64', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('65', plain,
% 0.51/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.51/0.68        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.51/0.68            = (k2_pre_topc @ sk_A @ 
% 0.51/0.68               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.51/0.68        | (v2_struct_0 @ sk_A)
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('demod', [status(thm)], ['63', '64'])).
% 0.51/0.68  thf('66', plain,
% 0.51/0.68      (((v2_struct_0 @ sk_A)
% 0.51/0.68        | ((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.51/0.68            = (k2_pre_topc @ sk_A @ 
% 0.51/0.68               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.51/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['65'])).
% 0.51/0.68  thf('67', plain,
% 0.51/0.68      (((k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.51/0.68         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('68', plain,
% 0.51/0.68      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.68      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.51/0.68  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('70', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.51/0.68      inference('clc', [status(thm)], ['68', '69'])).
% 0.51/0.68  thf(fc2_struct_0, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.51/0.68       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.68  thf('71', plain,
% 0.51/0.68      (![X8 : $i]:
% 0.51/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.51/0.68          | ~ (l1_struct_0 @ X8)
% 0.51/0.68          | (v2_struct_0 @ X8))),
% 0.51/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.51/0.68  thf('72', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.51/0.68      inference('sup-', [status(thm)], ['70', '71'])).
% 0.51/0.68  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf(dt_l1_pre_topc, axiom,
% 0.51/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.51/0.68  thf('74', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.51/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.51/0.68  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.51/0.68      inference('sup-', [status(thm)], ['73', '74'])).
% 0.51/0.68  thf('76', plain, ((v2_struct_0 @ sk_A)),
% 0.51/0.68      inference('demod', [status(thm)], ['72', '75'])).
% 0.51/0.68  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.51/0.68  
% 0.51/0.68  % SZS output end Refutation
% 0.51/0.68  
% 0.51/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
