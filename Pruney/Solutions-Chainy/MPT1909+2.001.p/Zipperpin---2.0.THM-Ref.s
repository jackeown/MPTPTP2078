%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tZhqT1VOn4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 425 expanded)
%              Number of leaves         :   39 ( 139 expanded)
%              Depth                    :   26
%              Number of atoms          : 1423 (12825 expanded)
%              Number of equality atoms :   29 ( 350 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_borsuk_1_type,type,(
    v3_borsuk_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v3_tex_2 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i] :
      ( ( v3_tex_2 @ ( sk_B @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t66_tex_2])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('9',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v4_tex_2 @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v3_borsuk_1 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( X24 != X25 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ X23 @ X24 )
        = ( k2_pre_topc @ X22 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v5_pre_topc @ X23 @ X22 @ X21 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v3_tdlat_3 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t76_tex_2])).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( v3_tdlat_3 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v5_pre_topc @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ X23 @ X25 )
        = ( k2_pre_topc @ X22 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_borsuk_1 @ X23 @ X22 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v4_tex_2 @ X21 @ X22 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ~ ( v3_borsuk_1 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v3_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_borsuk_1 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ X0 )
        = ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32','33','34','35','36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tarski @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k1_tarski @ sk_D ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D )
      = ( k1_tarski @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('43',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_D = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ sk_D ) )
 != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_D ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','48'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t66_tex_2])).

thf('53',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v3_tdlat_3 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc18_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tdlat_3 @ B )
           => ( v3_tdlat_3 @ B ) ) ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v3_tdlat_3 @ X14 )
      | ~ ( v1_tdlat_3 @ X14 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc18_tex_2])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v3_tdlat_3 @ sk_B_1 )
    | ~ ( v1_tdlat_3 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v4_tex_2 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( v4_tex_2 @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc35_tex_2])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( v4_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_tdlat_3 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_tdlat_3 @ sk_B_1 ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    v3_tdlat_3 @ sk_B_1 ),
    inference(demod,[status(thm)],['68','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('82',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56','61','79','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('89',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','90'])).

thf('92',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t66_tex_2])).

thf('93',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v3_tdlat_3 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['59','60'])).

thf('97',plain,(
    v3_tdlat_3 @ sk_B_1 ),
    inference(demod,[status(thm)],['68','78'])).

thf('98',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('99',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_xboole_0 @ ( sk_B @ sk_B_1 ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v3_tdlat_3 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t66_tex_2])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('106',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ~ ( v3_tex_2 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( v3_tdlat_3 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v3_tex_2 @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('111',plain,(
    v3_tdlat_3 @ sk_B_1 ),
    inference(demod,[status(thm)],['68','78'])).

thf('112',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['59','60'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( v3_tex_2 @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ~ ( v3_tex_2 @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( v3_tdlat_3 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('118',plain,(
    v3_tdlat_3 @ sk_B_1 ),
    inference(demod,[status(thm)],['68','78'])).

thf('119',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['59','60'])).

thf('120',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['0','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tZhqT1VOn4
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 172 iterations in 0.086s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.54  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.20/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.54  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(v3_borsuk_1_type, type, v3_borsuk_1: $i > $i > $i > $o).
% 0.20/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.54  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.54  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.20/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.54  thf(t77_tex_2, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.54             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.54                 ( m1_subset_1 @
% 0.20/0.54                   C @ 
% 0.20/0.54                   ( k1_zfmisc_1 @
% 0.20/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.54                 ( ![D:$i]:
% 0.20/0.54                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.54                     ( ![E:$i]:
% 0.20/0.54                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.54                           ( ( k8_relset_1 @
% 0.20/0.54                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.54                               ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.54                             ( k2_pre_topc @
% 0.20/0.54                               A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.54                ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.54                    ( v1_funct_2 @
% 0.20/0.54                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                    ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.54                    ( m1_subset_1 @
% 0.20/0.54                      C @ 
% 0.20/0.54                      ( k1_zfmisc_1 @
% 0.20/0.54                        ( k2_zfmisc_1 @
% 0.20/0.54                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54                  ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.54                    ( ![D:$i]:
% 0.20/0.54                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.54                        ( ![E:$i]:
% 0.20/0.54                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                            ( ( ( D ) = ( E ) ) =>
% 0.20/0.54                              ( ( k8_relset_1 @
% 0.20/0.54                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.54                                  C @ ( k6_domain_1 @ ( u1_struct_0 @ B ) @ D ) ) =
% 0.20/0.54                                ( k2_pre_topc @
% 0.20/0.54                                  A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ E ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t77_tex_2])).
% 0.20/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t66_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ?[B:$i]:
% 0.20/0.54         ( ( v3_tex_2 @ B @ A ) & 
% 0.20/0.54           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X20 : $i]:
% 0.20/0.54         ((v3_tex_2 @ (sk_B @ X20) @ X20)
% 0.20/0.54          | ~ (l1_pre_topc @ X20)
% 0.20/0.54          | ~ (v3_tdlat_3 @ X20)
% 0.20/0.54          | ~ (v2_pre_topc @ X20)
% 0.20/0.54          | (v2_struct_0 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t66_tex_2])).
% 0.20/0.54  thf('2', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('3', plain, (((sk_D) = (sk_E))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('4', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X12)
% 0.20/0.54          | ~ (m1_subset_1 @ X13 @ X12)
% 0.20/0.54          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X12)
% 0.20/0.54          | ~ (m1_subset_1 @ X13 @ X12)
% 0.20/0.54          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_k6_domain_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.54       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X10)
% 0.20/0.54          | ~ (m1_subset_1 @ X11 @ X10)
% 0.20/0.54          | (m1_subset_1 @ (k6_domain_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf(t39_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X7 @ X8)
% 0.20/0.54          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.54          | ~ (l1_pre_topc @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | ~ (l1_pre_topc @ X0)
% 0.20/0.54          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.54          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.54  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['9', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (((m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ 
% 0.20/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t76_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) & 
% 0.20/0.54             ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.54                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.54                 ( v5_pre_topc @ C @ A @ B ) & 
% 0.20/0.54                 ( m1_subset_1 @
% 0.20/0.54                   C @ 
% 0.20/0.54                   ( k1_zfmisc_1 @
% 0.20/0.54                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.54               ( ( v3_borsuk_1 @ C @ A @ B ) =>
% 0.20/0.54                 ( ![D:$i]:
% 0.20/0.54                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54                     ( ![E:$i]:
% 0.20/0.54                       ( ( m1_subset_1 @
% 0.20/0.54                           E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54                         ( ( ( D ) = ( E ) ) =>
% 0.20/0.54                           ( ( k8_relset_1 @
% 0.20/0.54                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.54                               D ) =
% 0.20/0.54                             ( k2_pre_topc @ A @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X21)
% 0.20/0.54          | ~ (v4_tex_2 @ X21 @ X22)
% 0.20/0.54          | ~ (m1_pre_topc @ X21 @ X22)
% 0.20/0.54          | ~ (v3_borsuk_1 @ X23 @ X22 @ X21)
% 0.20/0.54          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54          | ((X24) != (X25))
% 0.20/0.54          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ X23 @ 
% 0.20/0.54              X24) = (k2_pre_topc @ X22 @ X25))
% 0.20/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.54          | ~ (m1_subset_1 @ X23 @ 
% 0.20/0.54               (k1_zfmisc_1 @ 
% 0.20/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.20/0.54          | ~ (v5_pre_topc @ X23 @ X22 @ X21)
% 0.20/0.54          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.20/0.54          | ~ (v1_funct_1 @ X23)
% 0.20/0.54          | ~ (l1_pre_topc @ X22)
% 0.20/0.54          | ~ (v3_tdlat_3 @ X22)
% 0.20/0.54          | ~ (v2_pre_topc @ X22)
% 0.20/0.54          | (v2_struct_0 @ X22))),
% 0.20/0.54      inference('cnf', [status(esa)], [t76_tex_2])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X22)
% 0.20/0.54          | ~ (v2_pre_topc @ X22)
% 0.20/0.54          | ~ (v3_tdlat_3 @ X22)
% 0.20/0.54          | ~ (l1_pre_topc @ X22)
% 0.20/0.54          | ~ (v1_funct_1 @ X23)
% 0.20/0.54          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.20/0.54          | ~ (v5_pre_topc @ X23 @ X22 @ X21)
% 0.20/0.54          | ~ (m1_subset_1 @ X23 @ 
% 0.20/0.54               (k1_zfmisc_1 @ 
% 0.20/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))))
% 0.20/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.20/0.54          | ((k8_relset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ X23 @ 
% 0.20/0.54              X25) = (k2_pre_topc @ X22 @ X25))
% 0.20/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54          | ~ (v3_borsuk_1 @ X23 @ X22 @ X21)
% 0.20/0.54          | ~ (m1_pre_topc @ X21 @ X22)
% 0.20/0.54          | ~ (v4_tex_2 @ X21 @ X22)
% 0.20/0.54          | (v2_struct_0 @ X21))),
% 0.20/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.54          | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.54          | ~ (v3_borsuk_1 @ sk_C @ sk_A @ sk_B_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.20/0.54              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.20/0.54          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.54               (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54          | ~ (v3_tdlat_3 @ sk_A)
% 0.20/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['25', '27'])).
% 0.20/0.54  thf('29', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('30', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('31', plain, ((v3_borsuk_1 @ sk_C @ sk_A @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('32', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('36', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.54          | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.20/0.54              sk_C @ X0) = (k2_pre_topc @ sk_A @ X0))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54          | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)],
% 0.20/0.54                ['28', '29', '30', '31', '32', '33', '34', '35', '36', '37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (m1_subset_1 @ (k1_tarski @ sk_D) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.20/0.54            sk_C @ (k1_tarski @ sk_D))
% 0.20/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '38'])).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.20/0.54            sk_C @ (k1_tarski @ sk_D))
% 0.20/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['20', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 0.20/0.54            sk_C @ (k1_tarski @ sk_D))
% 0.20/0.54            = (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D) = (k1_tarski @ sk_D))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.20/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.20/0.54         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_E)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('44', plain, (((sk_D) = (sk_E))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.20/0.54         (k6_domain_1 @ (u1_struct_0 @ sk_B_1) @ sk_D))
% 0.20/0.54         != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.20/0.54          (k1_tarski @ sk_D))
% 0.20/0.54          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['42', '45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.54          != (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['41', '46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | ((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.54            != (k2_pre_topc @ sk_A @ 
% 0.20/0.54                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((((k2_pre_topc @ sk_A @ (k1_tarski @ sk_D))
% 0.20/0.54          != (k2_pre_topc @ sk_A @ (k1_tarski @ sk_D)))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.54  thf('51', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X20 : $i]:
% 0.20/0.54         ((m1_subset_1 @ (sk_B @ X20) @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.54          | ~ (l1_pre_topc @ X20)
% 0.20/0.54          | ~ (v3_tdlat_3 @ X20)
% 0.20/0.54          | ~ (v2_pre_topc @ X20)
% 0.20/0.54          | (v2_struct_0 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t66_tex_2])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X7 @ X8)
% 0.20/0.54          | (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.54          | ~ (l1_pre_topc @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X0)
% 0.20/0.54          | ~ (v2_pre_topc @ X0)
% 0.20/0.54          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.54          | ~ (l1_pre_topc @ X0)
% 0.20/0.54          | ~ (l1_pre_topc @ X1)
% 0.20/0.54          | (m1_subset_1 @ (sk_B @ X0) @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.54          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.54        | ~ (v3_tdlat_3 @ sk_B_1)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '54'])).
% 0.20/0.54  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('57', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_m1_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.54  thf('59', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('61', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.54  thf('62', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc18_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.54           ( ( v1_tdlat_3 @ B ) => ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (![X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.54          | (v3_tdlat_3 @ X14)
% 0.20/0.54          | ~ (v1_tdlat_3 @ X14)
% 0.20/0.54          | ~ (l1_pre_topc @ X15)
% 0.20/0.54          | (v2_struct_0 @ X15))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc18_tex_2])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ~ (v1_tdlat_3 @ sk_B_1)
% 0.20/0.54        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.54  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A) | ~ (v1_tdlat_3 @ sk_B_1) | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.54  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('68', plain, (((v3_tdlat_3 @ sk_B_1) | ~ (v1_tdlat_3 @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.54  thf('69', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc35_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.54           ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_tex_2 @ B @ A ) ) =>
% 0.20/0.54             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) ) ) ) ) ))).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      (![X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.54          | (v1_tdlat_3 @ X16)
% 0.20/0.54          | ~ (v4_tex_2 @ X16 @ X17)
% 0.20/0.54          | (v2_struct_0 @ X16)
% 0.20/0.54          | ~ (l1_pre_topc @ X17)
% 0.20/0.54          | (v2_struct_0 @ X17))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc35_tex_2])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | ~ (v4_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.54        | (v1_tdlat_3 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.54  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('73', plain, ((v4_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B_1) | (v1_tdlat_3 @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.20/0.54  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('76', plain, (((v1_tdlat_3 @ sk_B_1) | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.54  thf('77', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('78', plain, ((v1_tdlat_3 @ sk_B_1)),
% 0.20/0.54      inference('clc', [status(thm)], ['76', '77'])).
% 0.20/0.54  thf('79', plain, ((v3_tdlat_3 @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['68', '78'])).
% 0.20/0.54  thf('80', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc1_pre_topc, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X3 @ X4)
% 0.20/0.54          | (v2_pre_topc @ X3)
% 0.20/0.54          | ~ (l1_pre_topc @ X4)
% 0.20/0.54          | ~ (v2_pre_topc @ X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v2_pre_topc @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('85', plain, ((v2_pre_topc @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.20/0.54  thf('86', plain,
% 0.20/0.54      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['55', '56', '61', '79', '85'])).
% 0.20/0.54  thf('87', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('88', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.54  thf(cc1_subset_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.20/0.54          | (v1_xboole_0 @ X1)
% 0.20/0.54          | ~ (v1_xboole_0 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.54        | (v1_xboole_0 @ (sk_B @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ (sk_B @ sk_B_1)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '90'])).
% 0.20/0.54  thf('92', plain,
% 0.20/0.54      (![X20 : $i]:
% 0.20/0.54         ((m1_subset_1 @ (sk_B @ X20) @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.54          | ~ (l1_pre_topc @ X20)
% 0.20/0.54          | ~ (v3_tdlat_3 @ X20)
% 0.20/0.54          | ~ (v2_pre_topc @ X20)
% 0.20/0.54          | (v2_struct_0 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t66_tex_2])).
% 0.20/0.54  thf('93', plain,
% 0.20/0.54      (![X1 : $i, X2 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.20/0.54          | (v1_xboole_0 @ X1)
% 0.20/0.54          | ~ (v1_xboole_0 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X0)
% 0.20/0.54          | ~ (v2_pre_topc @ X0)
% 0.20/0.54          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.54          | ~ (l1_pre_topc @ X0)
% 0.20/0.54          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.54          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.54  thf('95', plain,
% 0.20/0.54      (((v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.20/0.54        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.54        | ~ (v3_tdlat_3 @ sk_B_1)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['91', '94'])).
% 0.20/0.54  thf('96', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.54  thf('97', plain, ((v3_tdlat_3 @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['68', '78'])).
% 0.20/0.54  thf('98', plain, ((v2_pre_topc @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      (((v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v1_xboole_0 @ (sk_B @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 0.20/0.54  thf('100', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (v2_struct_0 @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ (sk_B @ sk_B_1)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['99'])).
% 0.20/0.54  thf('101', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('102', plain, (((v1_xboole_0 @ (sk_B @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.54  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('104', plain, ((v1_xboole_0 @ (sk_B @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['102', '103'])).
% 0.20/0.54  thf('105', plain,
% 0.20/0.54      (![X20 : $i]:
% 0.20/0.54         ((m1_subset_1 @ (sk_B @ X20) @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.54          | ~ (l1_pre_topc @ X20)
% 0.20/0.54          | ~ (v3_tdlat_3 @ X20)
% 0.20/0.54          | ~ (v2_pre_topc @ X20)
% 0.20/0.54          | (v2_struct_0 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t66_tex_2])).
% 0.20/0.54  thf(t46_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( v1_xboole_0 @ B ) & 
% 0.20/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('106', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (v1_xboole_0 @ X18)
% 0.20/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.54          | ~ (v3_tex_2 @ X18 @ X19)
% 0.20/0.54          | ~ (l1_pre_topc @ X19)
% 0.20/0.54          | ~ (v2_pre_topc @ X19)
% 0.20/0.54          | (v2_struct_0 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [t46_tex_2])).
% 0.20/0.55  thf('107', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v2_struct_0 @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | (v2_struct_0 @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.20/0.55          | ~ (v1_xboole_0 @ (sk_B @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.55  thf('108', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_xboole_0 @ (sk_B @ X0))
% 0.20/0.55          | ~ (v3_tex_2 @ (sk_B @ X0) @ X0)
% 0.20/0.55          | ~ (l1_pre_topc @ X0)
% 0.20/0.55          | ~ (v3_tdlat_3 @ X0)
% 0.20/0.55          | ~ (v2_pre_topc @ X0)
% 0.20/0.55          | (v2_struct_0 @ X0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['107'])).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_B_1)
% 0.20/0.55        | ~ (v3_tdlat_3 @ sk_B_1)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.55        | ~ (v3_tex_2 @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['104', '108'])).
% 0.20/0.55  thf('110', plain, ((v2_pre_topc @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.20/0.55  thf('111', plain, ((v3_tdlat_3 @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '78'])).
% 0.20/0.55  thf('112', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1) | ~ (v3_tex_2 @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.20/0.55  thf('114', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('115', plain, (~ (v3_tex_2 @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.20/0.55      inference('clc', [status(thm)], ['113', '114'])).
% 0.20/0.55  thf('116', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_B_1)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_B_1)
% 0.20/0.55        | ~ (v3_tdlat_3 @ sk_B_1)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '115'])).
% 0.20/0.55  thf('117', plain, ((v2_pre_topc @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.20/0.55  thf('118', plain, ((v3_tdlat_3 @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '78'])).
% 0.20/0.55  thf('119', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf('120', plain, ((v2_struct_0 @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.20/0.55  thf('121', plain, ($false), inference('demod', [status(thm)], ['0', '120'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
