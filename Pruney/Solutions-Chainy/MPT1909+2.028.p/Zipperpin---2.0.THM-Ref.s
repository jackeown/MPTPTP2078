%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y14w0lv93R

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 194 expanded)
%              Number of leaves         :   34 (  73 expanded)
%              Depth                    :   23
%              Number of atoms          :  994 (5087 expanded)
%              Number of equality atoms :   31 ( 155 expanded)
%              Maximal formula depth    :   23 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t77_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                            = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( v3_borsuk_1 @ C @ A @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                     => ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( D = E )
                           => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) )
                              = ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( ( k6_domain_1 @ X8 @ X9 )
        = ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('7',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( ( k6_domain_1 @ X8 @ X9 )
        = ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('16',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t76_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_tex_2 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( v5_pre_topc @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v3_borsuk_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( D = E )
                         => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D )
                            = ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v4_tex_2 @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v3_borsuk_1 @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X13 != X14 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) @ X12 @ X13 )
        = ( k2_pre_topc @ X11 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v5_pre_topc @ X12 @ X11 @ X10 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( v3_tdlat_3 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( v5_pre_topc @ X12 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) @ X12 @ X14 )
        = ( k2_pre_topc @ X11 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_borsuk_1 @ X12 @ X11 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v4_tex_2 @ X10 @ X11 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v4_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v4_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30','31','32','33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','36'])).

thf('38',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('39',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','51'])).

thf('53',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','59'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('61',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('73',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y14w0lv93R
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 458 iterations in 0.192s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.64  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.64  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.46/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.64  thf(t77_tex_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.64         ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.64             ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.64                 ( m1_subset_1 @
% 0.46/0.64                   C @ 
% 0.46/0.64                   ( k1_zfmisc_1 @
% 0.46/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.64                 ( ![D:$i]:
% 0.46/0.64                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.64                     ( ![E:$i]:
% 0.46/0.64                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64                         ( ( ( D ) = ( E ) ) =>
% 0.46/0.64                           ( ( k8_relset_1 @
% 0.46/0.64                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.64                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.46/0.64                             ( k2_pre_topc @
% 0.46/0.64                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.64            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.64                ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.64              ( ![C:$i]:
% 0.46/0.64                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                    ( v1_funct_2 @
% 0.46/0.64                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.64                    ( m1_subset_1 @
% 0.46/0.64                      C @ 
% 0.46/0.64                      ( k1_zfmisc_1 @
% 0.46/0.64                        ( k2_zfmisc_1 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.64                    ( ![D:$i]:
% 0.46/0.64                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.46/0.64                        ( ![E:$i]:
% 0.46/0.64                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.64                            ( ( ( D ) = ( E ) ) =>
% 0.46/0.64                              ( ( k8_relset_1 @
% 0.46/0.64                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.64                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.46/0.64                                ( k2_pre_topc @
% 0.46/0.64                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.46/0.64  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(d3_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X1 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X1) = (u1_struct_0 @ X1)) | ~ (l1_struct_0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('3', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain, (((sk_D) = (sk_E))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('5', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(redefinition_k6_domain_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.64       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X8)
% 0.46/0.64          | ~ (m1_subset_1 @ X9 @ X8)
% 0.46/0.64          | ((k6_domain_1 @ X8 @ X9) = (k1_tarski @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('9', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf(dt_k6_domain_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.46/0.64       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X6)
% 0.46/0.64          | ~ (m1_subset_1 @ X7 @ X6)
% 0.46/0.64          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.46/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['8', '11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.64  thf('14', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X8)
% 0.46/0.64          | ~ (m1_subset_1 @ X9 @ X8)
% 0.46/0.64          | ((k6_domain_1 @ X8 @ X9) = (k1_tarski @ X9)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('17', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X6)
% 0.46/0.64          | ~ (m1_subset_1 @ X7 @ X6)
% 0.46/0.64          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.46/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['16', '19'])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t76_tex_2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.46/0.64         ( l1_pre_topc @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.46/0.64             ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.46/0.64                 ( m1_subset_1 @
% 0.46/0.64                   C @ 
% 0.46/0.64                   ( k1_zfmisc_1 @
% 0.46/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.46/0.64                 ( ![D:$i]:
% 0.46/0.64                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.64                     ( ![E:$i]:
% 0.46/0.64                       ( ( m1_subset_1 @
% 0.46/0.64                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.64                         ( ( ( D ) = ( E ) ) =>
% 0.46/0.64                           ( ( k8_relset_1 @
% 0.46/0.64                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.64                               D ) =
% 0.46/0.64                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X10)
% 0.46/0.64          | ~ (v4_tex_2 @ X10 @ X11)
% 0.46/0.64          | ~ (m1_pre_topc @ X10 @ X11)
% 0.46/0.64          | ~ (v3_borsuk_1 @ X12 @ X11 @ X10)
% 0.46/0.64          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.64          | ((X13) != (X14))
% 0.46/0.64          | ((k8_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10) @ X12 @ 
% 0.46/0.64              X13) = (k2_pre_topc @ X11 @ X14))
% 0.46/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.64          | ~ (m1_subset_1 @ X12 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10))))
% 0.46/0.64          | ~ (v5_pre_topc @ X12 @ X11 @ X10)
% 0.46/0.64          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10))
% 0.46/0.64          | ~ (v1_funct_1 @ X12)
% 0.46/0.64          | ~ (l1_pre_topc @ X11)
% 0.46/0.64          | ~ (v3_tdlat_3 @ X11)
% 0.46/0.64          | ~ (v2_pre_topc @ X11)
% 0.46/0.64          | (v2_struct_0 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.46/0.64         ((v2_struct_0 @ X11)
% 0.46/0.64          | ~ (v2_pre_topc @ X11)
% 0.46/0.64          | ~ (v3_tdlat_3 @ X11)
% 0.46/0.64          | ~ (l1_pre_topc @ X11)
% 0.46/0.64          | ~ (v1_funct_1 @ X12)
% 0.46/0.64          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10))
% 0.46/0.64          | ~ (v5_pre_topc @ X12 @ X11 @ X10)
% 0.46/0.64          | ~ (m1_subset_1 @ X12 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10))))
% 0.46/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.64          | ((k8_relset_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10) @ X12 @ 
% 0.46/0.64              X14) = (k2_pre_topc @ X11 @ X14))
% 0.46/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.64          | ~ (v3_borsuk_1 @ X12 @ X11 @ X10)
% 0.46/0.64          | ~ (m1_pre_topc @ X10 @ X11)
% 0.46/0.64          | ~ (v4_tex_2 @ X10 @ X11)
% 0.46/0.64          | (v2_struct_0 @ X10))),
% 0.46/0.64      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_B)
% 0.46/0.64          | ~ (v4_tex_2 @ sk_B @ sk_A)
% 0.46/0.64          | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.64          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.64          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.64          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.46/0.64          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.64          | ~ (v3_tdlat_3 @ sk_A)
% 0.46/0.64          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.64          | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '24'])).
% 0.46/0.64  thf('26', plain, ((v4_tex_2 @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('28', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('29', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('33', plain, ((v3_tdlat_3 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v2_struct_0 @ sk_B)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.46/0.64          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.64          | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['25', '26', '27', '28', '29', '30', '31', '32', '33', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.46/0.64             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.64        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.64        | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['21', '35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64            (k1_tarski @ sk_D)) = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['13', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      ((((k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D) = (k1_tarski @ sk_D))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.46/0.64         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('40', plain, (((sk_D) = (sk_E))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64         (k6_domain_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.46/0.64         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.46/0.64      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64          (k1_tarski @ sk_D))
% 0.46/0.64          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.64          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.64            != (k2_pre_topc @ sk_A @ 
% 0.46/0.64                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['43'])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.46/0.64          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '44'])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['2', '46'])).
% 0.46/0.64  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(dt_l1_pre_topc, axiom,
% 0.46/0.64    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.64  thf('49', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.64  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['47', '50'])).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['1', '51'])).
% 0.46/0.64  thf('53', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(dt_m1_pre_topc, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_pre_topc @ A ) =>
% 0.46/0.64       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.64  thf('55', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.64      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.64  thf('58', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.64  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['52', '59'])).
% 0.46/0.64  thf(fc5_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.64       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X5 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ (k2_struct_0 @ X5))
% 0.46/0.64          | ~ (l1_struct_0 @ X5)
% 0.46/0.64          | (v2_struct_0 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_A)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.64  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A)
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | (v2_struct_0 @ sk_A))),
% 0.46/0.64      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.64  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 0.46/0.64      inference('clc', [status(thm)], ['65', '66'])).
% 0.46/0.64  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('69', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('clc', [status(thm)], ['67', '68'])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      (![X5 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ (k2_struct_0 @ X5))
% 0.46/0.64          | ~ (l1_struct_0 @ X5)
% 0.46/0.64          | (v2_struct_0 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.46/0.64  thf('71', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.64  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('73', plain, ((v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.64  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.49/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
