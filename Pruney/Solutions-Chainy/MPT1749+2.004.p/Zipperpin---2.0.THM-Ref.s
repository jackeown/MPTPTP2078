%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BDpOjgtULo

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:38 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  202 (1471 expanded)
%              Number of leaves         :   41 ( 445 expanded)
%              Depth                    :   32
%              Number of atoms          : 2340 (58115 expanded)
%              Number of equality atoms :   34 ( 811 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t59_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                = ( k1_funct_1 @ E @ F ) ) ) )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) )
                       => ( ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                             => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                               => ( ( k3_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ F )
                                  = ( k1_funct_1 @ E @ F ) ) ) )
                         => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_tmap_1])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ( ( k2_tmap_1 @ X31 @ X29 @ X32 @ X30 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) @ X32 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k2_partfun1 @ X18 @ X19 @ X17 @ X20 )
        = ( k7_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10','15','16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X34 )
      | ~ ( l1_struct_0 @ X36 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X34 @ X35 @ X33 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['23','37'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( l1_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('47',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r2_funct_2 @ A @ B @ C @ D )
          <=> ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X12 @ X15 @ X13 ) @ X13 )
      | ( r2_funct_2 @ X13 @ X14 @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_E_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_E_1 )
      | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('56',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X34 )
      | ~ ( l1_struct_0 @ X36 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X34 @ X35 @ X33 @ X36 ) @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('73',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('75',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('76',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X34 )
      | ~ ( l1_struct_0 @ X36 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X34 @ X35 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','89'])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['74','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('93',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['53','73','93'])).

thf('95',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('97',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['94','97'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X39: $i] :
      ( ~ ( r2_hidden @ X39 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X39 )
        = ( k1_funct_1 @ sk_E_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('103',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('107',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X39: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X39 )
        = ( k1_funct_1 @ sk_E_1 @ X39 ) )
      | ~ ( r2_hidden @ X39 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['101','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['100','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('115',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ X22 )
      | ( ( k3_funct_2 @ X22 @ X23 @ X21 @ X24 )
        = ( k1_funct_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,
    ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['110','120'])).

thf('122',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('124',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X11 @ X10 ) @ X9 )
        = ( k1_funct_1 @ X11 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k1_funct_1 @ X15 @ ( sk_E @ X12 @ X15 @ X13 ) )
       != ( k1_funct_1 @ X12 @ ( sk_E @ X12 @ X15 @ X13 ) ) )
      | ( r2_funct_2 @ X13 @ X14 @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( v1_funct_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('129',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('131',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('132',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('135',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['127','132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['122','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','138'])).

thf('140',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('143',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('146',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('152',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('154',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    $false ),
    inference(demod,[status(thm)],['157','158'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BDpOjgtULo
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.76  % Solved by: fo/fo7.sh
% 0.52/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.76  % done 401 iterations in 0.304s
% 0.52/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.76  % SZS output start Refutation
% 0.52/0.76  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.52/0.76  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.52/0.76  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.52/0.76  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.52/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.76  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.52/0.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.52/0.76  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.52/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.76  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.52/0.76  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.52/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.76  thf(dt_l1_pre_topc, axiom,
% 0.52/0.76    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.52/0.76  thf('0', plain, (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('1', plain, (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('2', plain, (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf(t59_tmap_1, conjecture,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.76       ( ![B:$i]:
% 0.52/0.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.52/0.76             ( l1_pre_topc @ B ) ) =>
% 0.52/0.76           ( ![C:$i]:
% 0.52/0.76             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.52/0.76               ( ![D:$i]:
% 0.52/0.76                 ( ( ( v1_funct_1 @ D ) & 
% 0.52/0.76                     ( v1_funct_2 @
% 0.52/0.76                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.52/0.76                     ( m1_subset_1 @
% 0.52/0.76                       D @ 
% 0.52/0.76                       ( k1_zfmisc_1 @
% 0.52/0.76                         ( k2_zfmisc_1 @
% 0.52/0.76                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.52/0.76                   ( ![E:$i]:
% 0.52/0.76                     ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.76                         ( v1_funct_2 @
% 0.52/0.76                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.52/0.76                         ( m1_subset_1 @
% 0.52/0.76                           E @ 
% 0.52/0.76                           ( k1_zfmisc_1 @
% 0.52/0.76                             ( k2_zfmisc_1 @
% 0.52/0.76                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.52/0.76                       ( ( ![F:$i]:
% 0.52/0.76                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.52/0.76                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.52/0.76                               ( ( k3_funct_2 @
% 0.52/0.76                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.52/0.76                                   D @ F ) =
% 0.52/0.76                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.52/0.76                         ( r2_funct_2 @
% 0.52/0.76                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.52/0.76                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.76    (~( ![A:$i]:
% 0.52/0.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.52/0.76            ( l1_pre_topc @ A ) ) =>
% 0.52/0.76          ( ![B:$i]:
% 0.52/0.76            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.52/0.76                ( l1_pre_topc @ B ) ) =>
% 0.52/0.76              ( ![C:$i]:
% 0.52/0.76                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.52/0.76                  ( ![D:$i]:
% 0.52/0.76                    ( ( ( v1_funct_1 @ D ) & 
% 0.52/0.76                        ( v1_funct_2 @
% 0.52/0.76                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.52/0.76                        ( m1_subset_1 @
% 0.52/0.76                          D @ 
% 0.52/0.76                          ( k1_zfmisc_1 @
% 0.52/0.76                            ( k2_zfmisc_1 @
% 0.52/0.76                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.52/0.76                      ( ![E:$i]:
% 0.52/0.76                        ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.76                            ( v1_funct_2 @
% 0.52/0.76                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.52/0.76                            ( m1_subset_1 @
% 0.52/0.76                              E @ 
% 0.52/0.76                              ( k1_zfmisc_1 @
% 0.52/0.76                                ( k2_zfmisc_1 @
% 0.52/0.76                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.52/0.76                          ( ( ![F:$i]:
% 0.52/0.76                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.52/0.76                                ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.52/0.76                                  ( ( k3_funct_2 @
% 0.52/0.76                                      ( u1_struct_0 @ B ) @ 
% 0.52/0.76                                      ( u1_struct_0 @ A ) @ D @ F ) =
% 0.52/0.76                                    ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.52/0.76                            ( r2_funct_2 @
% 0.52/0.76                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.52/0.76                              ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.76    inference('cnf.neg', [status(esa)], [t59_tmap_1])).
% 0.52/0.76  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('4', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_D @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(d4_tmap_1, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.76       ( ![B:$i]:
% 0.52/0.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.52/0.76             ( l1_pre_topc @ B ) ) =>
% 0.52/0.76           ( ![C:$i]:
% 0.52/0.76             ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.76                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.76                 ( m1_subset_1 @
% 0.52/0.76                   C @ 
% 0.52/0.76                   ( k1_zfmisc_1 @
% 0.52/0.76                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.52/0.76               ( ![D:$i]:
% 0.52/0.76                 ( ( m1_pre_topc @ D @ A ) =>
% 0.52/0.76                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.52/0.76                     ( k2_partfun1 @
% 0.52/0.76                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.52/0.76                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.76  thf('5', plain,
% 0.52/0.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.76         ((v2_struct_0 @ X29)
% 0.52/0.76          | ~ (v2_pre_topc @ X29)
% 0.52/0.76          | ~ (l1_pre_topc @ X29)
% 0.52/0.76          | ~ (m1_pre_topc @ X30 @ X31)
% 0.52/0.76          | ((k2_tmap_1 @ X31 @ X29 @ X32 @ X30)
% 0.52/0.76              = (k2_partfun1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29) @ 
% 0.52/0.76                 X32 @ (u1_struct_0 @ X30)))
% 0.52/0.76          | ~ (m1_subset_1 @ X32 @ 
% 0.52/0.76               (k1_zfmisc_1 @ 
% 0.52/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))))
% 0.52/0.76          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))
% 0.52/0.76          | ~ (v1_funct_1 @ X32)
% 0.52/0.76          | ~ (l1_pre_topc @ X31)
% 0.52/0.76          | ~ (v2_pre_topc @ X31)
% 0.52/0.76          | (v2_struct_0 @ X31))),
% 0.52/0.76      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v2_struct_0 @ sk_B)
% 0.52/0.76          | ~ (v2_pre_topc @ sk_B)
% 0.52/0.76          | ~ (l1_pre_topc @ sk_B)
% 0.52/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.52/0.76          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.52/0.76              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76                 sk_D @ (u1_struct_0 @ X0)))
% 0.52/0.76          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.52/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.52/0.76          | ~ (v2_pre_topc @ sk_A)
% 0.52/0.76          | (v2_struct_0 @ sk_A))),
% 0.52/0.76      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.76  thf('7', plain, ((v2_pre_topc @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('11', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_D @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(redefinition_k2_partfun1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.76       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.52/0.76  thf('12', plain,
% 0.52/0.76      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.52/0.76          | ~ (v1_funct_1 @ X17)
% 0.52/0.76          | ((k2_partfun1 @ X18 @ X19 @ X17 @ X20) = (k7_relat_1 @ X17 @ X20)))),
% 0.52/0.76      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.52/0.76  thf('13', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.52/0.76            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.52/0.76          | ~ (v1_funct_1 @ sk_D))),
% 0.52/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.76  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.52/0.76           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.76  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v2_struct_0 @ sk_B)
% 0.52/0.76          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.52/0.76              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.52/0.76          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.52/0.76          | (v2_struct_0 @ sk_A))),
% 0.52/0.76      inference('demod', [status(thm)],
% 0.52/0.76                ['6', '7', '8', '9', '10', '15', '16', '17'])).
% 0.52/0.76  thf('19', plain,
% 0.52/0.76      (((v2_struct_0 @ sk_A)
% 0.52/0.76        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.52/0.76            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.52/0.76        | (v2_struct_0 @ sk_B))),
% 0.52/0.76      inference('sup-', [status(thm)], ['3', '18'])).
% 0.52/0.76  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('21', plain,
% 0.52/0.76      (((v2_struct_0 @ sk_B)
% 0.52/0.76        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.52/0.76            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.52/0.76      inference('clc', [status(thm)], ['19', '20'])).
% 0.52/0.76  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('23', plain,
% 0.52/0.76      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.52/0.76         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('clc', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('24', plain,
% 0.52/0.76      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('25', plain,
% 0.52/0.76      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('26', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_D @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(dt_k2_tmap_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.52/0.76         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.52/0.76         ( m1_subset_1 @
% 0.52/0.76           C @ 
% 0.52/0.76           ( k1_zfmisc_1 @
% 0.52/0.76             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.52/0.76         ( l1_struct_0 @ D ) ) =>
% 0.52/0.76       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.52/0.76         ( v1_funct_2 @
% 0.52/0.76           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.52/0.76           ( u1_struct_0 @ B ) ) & 
% 0.52/0.76         ( m1_subset_1 @
% 0.52/0.76           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.52/0.76           ( k1_zfmisc_1 @
% 0.52/0.76             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.52/0.76  thf('27', plain,
% 0.52/0.76      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X33 @ 
% 0.52/0.76             (k1_zfmisc_1 @ 
% 0.52/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))))
% 0.52/0.76          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))
% 0.52/0.76          | ~ (v1_funct_1 @ X33)
% 0.52/0.76          | ~ (l1_struct_0 @ X35)
% 0.52/0.76          | ~ (l1_struct_0 @ X34)
% 0.52/0.76          | ~ (l1_struct_0 @ X36)
% 0.52/0.76          | (m1_subset_1 @ (k2_tmap_1 @ X34 @ X35 @ X33 @ X36) @ 
% 0.52/0.76             (k1_zfmisc_1 @ 
% 0.52/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X35)))))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.52/0.76  thf('28', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76           (k1_zfmisc_1 @ 
% 0.52/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.52/0.76          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.76  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('30', plain,
% 0.52/0.76      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('31', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76           (k1_zfmisc_1 @ 
% 0.52/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.76      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.52/0.76  thf('32', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_pre_topc @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76             (k1_zfmisc_1 @ 
% 0.52/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['25', '31'])).
% 0.52/0.76  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('34', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76             (k1_zfmisc_1 @ 
% 0.52/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 0.52/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.52/0.76  thf('35', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_pre_topc @ sk_A)
% 0.52/0.76          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76             (k1_zfmisc_1 @ 
% 0.52/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76          | ~ (l1_struct_0 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['24', '34'])).
% 0.52/0.76  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('37', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76           (k1_zfmisc_1 @ 
% 0.52/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76          | ~ (l1_struct_0 @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['35', '36'])).
% 0.52/0.76  thf('38', plain,
% 0.52/0.76      (((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76         (k1_zfmisc_1 @ 
% 0.52/0.76          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76        | ~ (l1_struct_0 @ sk_C))),
% 0.52/0.76      inference('sup+', [status(thm)], ['23', '37'])).
% 0.52/0.76  thf('39', plain,
% 0.52/0.76      ((~ (l1_pre_topc @ sk_C)
% 0.52/0.76        | (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76           (k1_zfmisc_1 @ 
% 0.52/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['2', '38'])).
% 0.52/0.76  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(dt_m1_pre_topc, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( l1_pre_topc @ A ) =>
% 0.52/0.76       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.52/0.76  thf('41', plain,
% 0.52/0.76      (![X26 : $i, X27 : $i]:
% 0.52/0.76         (~ (m1_pre_topc @ X26 @ X27)
% 0.52/0.76          | (l1_pre_topc @ X26)
% 0.52/0.76          | ~ (l1_pre_topc @ X27))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.52/0.76  thf('42', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.76  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 0.52/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.76  thf('45', plain,
% 0.52/0.76      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('demod', [status(thm)], ['39', '44'])).
% 0.52/0.76  thf('46', plain,
% 0.52/0.76      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('demod', [status(thm)], ['39', '44'])).
% 0.52/0.76  thf('47', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E_1 @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(d9_funct_2, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.76       ( ![D:$i]:
% 0.52/0.76         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.52/0.76             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.76           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 0.52/0.76             ( ![E:$i]:
% 0.52/0.76               ( ( m1_subset_1 @ E @ A ) =>
% 0.52/0.76                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 0.52/0.76  thf('48', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.76         (~ (v1_funct_1 @ X12)
% 0.52/0.76          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.52/0.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.52/0.76          | (m1_subset_1 @ (sk_E @ X12 @ X15 @ X13) @ X13)
% 0.52/0.76          | (r2_funct_2 @ X13 @ X14 @ X15 @ X12)
% 0.52/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.52/0.76          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.52/0.76          | ~ (v1_funct_1 @ X15))),
% 0.52/0.76      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.52/0.76  thf('49', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (v1_funct_1 @ X0)
% 0.52/0.76          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (m1_subset_1 @ X0 @ 
% 0.52/0.76               (k1_zfmisc_1 @ 
% 0.52/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.52/0.76             sk_E_1)
% 0.52/0.76          | (m1_subset_1 @ (sk_E @ sk_E_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C))
% 0.52/0.76          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.52/0.76               (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (v1_funct_1 @ sk_E_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.52/0.76  thf('50', plain,
% 0.52/0.76      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('51', plain, ((v1_funct_1 @ sk_E_1)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('52', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (v1_funct_1 @ X0)
% 0.52/0.76          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (m1_subset_1 @ X0 @ 
% 0.52/0.76               (k1_zfmisc_1 @ 
% 0.52/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.52/0.76             sk_E_1)
% 0.52/0.76          | (m1_subset_1 @ (sk_E @ sk_E_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.52/0.76  thf('53', plain,
% 0.52/0.76      (((m1_subset_1 @ 
% 0.52/0.76         (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76          (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76         (u1_struct_0 @ sk_C))
% 0.52/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.52/0.76        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.52/0.76        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['46', '52'])).
% 0.52/0.76  thf('54', plain,
% 0.52/0.76      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('55', plain,
% 0.52/0.76      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.52/0.76         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('clc', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('56', plain,
% 0.52/0.76      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('57', plain,
% 0.52/0.76      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('58', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_D @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('59', plain,
% 0.52/0.76      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X33 @ 
% 0.52/0.76             (k1_zfmisc_1 @ 
% 0.52/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))))
% 0.52/0.76          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))
% 0.52/0.76          | ~ (v1_funct_1 @ X33)
% 0.52/0.76          | ~ (l1_struct_0 @ X35)
% 0.52/0.76          | ~ (l1_struct_0 @ X34)
% 0.52/0.76          | ~ (l1_struct_0 @ X36)
% 0.52/0.76          | (v1_funct_2 @ (k2_tmap_1 @ X34 @ X35 @ X33 @ X36) @ 
% 0.52/0.76             (u1_struct_0 @ X36) @ (u1_struct_0 @ X35)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.52/0.76  thf('60', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.52/0.76          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.76  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('62', plain,
% 0.52/0.76      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('63', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.76      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.52/0.76  thf('64', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_pre_topc @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['57', '63'])).
% 0.52/0.76  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('66', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('demod', [status(thm)], ['64', '65'])).
% 0.52/0.76  thf('67', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_pre_topc @ sk_A)
% 0.52/0.76          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (l1_struct_0 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['56', '66'])).
% 0.52/0.76  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('69', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.52/0.76           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.52/0.76          | ~ (l1_struct_0 @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.76  thf('70', plain,
% 0.52/0.76      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.52/0.76        | ~ (l1_struct_0 @ sk_C))),
% 0.52/0.76      inference('sup+', [status(thm)], ['55', '69'])).
% 0.52/0.76  thf('71', plain,
% 0.52/0.76      ((~ (l1_pre_topc @ sk_C)
% 0.52/0.76        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['54', '70'])).
% 0.52/0.76  thf('72', plain, ((l1_pre_topc @ sk_C)),
% 0.52/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.76  thf('73', plain,
% 0.52/0.76      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('demod', [status(thm)], ['71', '72'])).
% 0.52/0.76  thf('74', plain,
% 0.52/0.76      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('75', plain,
% 0.52/0.76      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.52/0.76         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('clc', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('76', plain,
% 0.52/0.76      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('77', plain,
% 0.52/0.76      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.76  thf('78', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_D @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('79', plain,
% 0.52/0.76      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X33 @ 
% 0.52/0.76             (k1_zfmisc_1 @ 
% 0.52/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))))
% 0.52/0.76          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X35))
% 0.52/0.76          | ~ (v1_funct_1 @ X33)
% 0.52/0.76          | ~ (l1_struct_0 @ X35)
% 0.52/0.76          | ~ (l1_struct_0 @ X34)
% 0.52/0.76          | ~ (l1_struct_0 @ X36)
% 0.52/0.76          | (v1_funct_1 @ (k2_tmap_1 @ X34 @ X35 @ X33 @ X36)))),
% 0.52/0.76      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.52/0.76  thf('80', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0))
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.52/0.76          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['78', '79'])).
% 0.52/0.76  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('82', plain,
% 0.52/0.76      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('83', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0))
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A))),
% 0.52/0.76      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.52/0.76  thf('84', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_pre_topc @ sk_B)
% 0.52/0.76          | ~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['77', '83'])).
% 0.52/0.76  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('86', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_struct_0 @ sk_A)
% 0.52/0.76          | ~ (l1_struct_0 @ X0)
% 0.52/0.76          | (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)))),
% 0.52/0.76      inference('demod', [status(thm)], ['84', '85'])).
% 0.52/0.76  thf('87', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (l1_pre_topc @ sk_A)
% 0.52/0.76          | (v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0))
% 0.52/0.76          | ~ (l1_struct_0 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['76', '86'])).
% 0.52/0.76  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('89', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v1_funct_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0))
% 0.52/0.76          | ~ (l1_struct_0 @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.76  thf('90', plain,
% 0.52/0.76      (((v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.52/0.76        | ~ (l1_struct_0 @ sk_C))),
% 0.52/0.76      inference('sup+', [status(thm)], ['75', '89'])).
% 0.52/0.76  thf('91', plain,
% 0.52/0.76      ((~ (l1_pre_topc @ sk_C)
% 0.52/0.76        | (v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['74', '90'])).
% 0.52/0.76  thf('92', plain, ((l1_pre_topc @ sk_C)),
% 0.52/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.76  thf('93', plain, ((v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('demod', [status(thm)], ['91', '92'])).
% 0.52/0.76  thf('94', plain,
% 0.52/0.76      (((m1_subset_1 @ 
% 0.52/0.76         (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76          (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76         (u1_struct_0 @ sk_C))
% 0.52/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1))),
% 0.52/0.76      inference('demod', [status(thm)], ['53', '73', '93'])).
% 0.52/0.76  thf('95', plain,
% 0.52/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E_1)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('96', plain,
% 0.52/0.76      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.52/0.76         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('clc', [status(thm)], ['21', '22'])).
% 0.52/0.76  thf('97', plain,
% 0.52/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)),
% 0.52/0.76      inference('demod', [status(thm)], ['95', '96'])).
% 0.52/0.76  thf('98', plain,
% 0.52/0.76      ((m1_subset_1 @ 
% 0.52/0.76        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76         (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76        (u1_struct_0 @ sk_C))),
% 0.52/0.76      inference('clc', [status(thm)], ['94', '97'])).
% 0.52/0.76  thf(t2_subset, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( m1_subset_1 @ A @ B ) =>
% 0.52/0.76       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.52/0.76  thf('99', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ X1)
% 0.52/0.76          | (v1_xboole_0 @ X1)
% 0.52/0.76          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.52/0.76      inference('cnf', [status(esa)], [t2_subset])).
% 0.52/0.76  thf('100', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | (r2_hidden @ 
% 0.52/0.76           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76            (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['98', '99'])).
% 0.52/0.76  thf('101', plain,
% 0.52/0.76      (![X39 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X39 @ (u1_struct_0 @ sk_C))
% 0.52/0.76          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76              sk_D @ X39) = (k1_funct_1 @ sk_E_1 @ X39))
% 0.52/0.76          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('102', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t1_tsep_1, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( l1_pre_topc @ A ) =>
% 0.52/0.76       ( ![B:$i]:
% 0.52/0.76         ( ( m1_pre_topc @ B @ A ) =>
% 0.52/0.76           ( m1_subset_1 @
% 0.52/0.76             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.52/0.76  thf('103', plain,
% 0.52/0.76      (![X37 : $i, X38 : $i]:
% 0.52/0.76         (~ (m1_pre_topc @ X37 @ X38)
% 0.52/0.76          | (m1_subset_1 @ (u1_struct_0 @ X37) @ 
% 0.52/0.76             (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.52/0.76          | ~ (l1_pre_topc @ X38))),
% 0.52/0.76      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.52/0.76  thf('104', plain,
% 0.52/0.76      ((~ (l1_pre_topc @ sk_B)
% 0.52/0.76        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.52/0.76           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['102', '103'])).
% 0.52/0.76  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('106', plain,
% 0.52/0.76      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.52/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.76      inference('demod', [status(thm)], ['104', '105'])).
% 0.52/0.76  thf(t4_subset, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.52/0.76       ( m1_subset_1 @ A @ C ) ))).
% 0.52/0.76  thf('107', plain,
% 0.52/0.76      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X2 @ X3)
% 0.52/0.76          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.52/0.76          | (m1_subset_1 @ X2 @ X4))),
% 0.52/0.76      inference('cnf', [status(esa)], [t4_subset])).
% 0.52/0.76  thf('108', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['106', '107'])).
% 0.52/0.76  thf('109', plain,
% 0.52/0.76      (![X39 : $i]:
% 0.52/0.76         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.52/0.76            X39) = (k1_funct_1 @ sk_E_1 @ X39))
% 0.52/0.76          | ~ (r2_hidden @ X39 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('clc', [status(thm)], ['101', '108'])).
% 0.52/0.76  thf('110', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.52/0.76            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C)))
% 0.52/0.76            = (k1_funct_1 @ sk_E_1 @ 
% 0.52/0.76               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76                (u1_struct_0 @ sk_C)))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['100', '109'])).
% 0.52/0.76  thf('111', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | (r2_hidden @ 
% 0.52/0.76           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76            (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['98', '99'])).
% 0.52/0.76  thf('112', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['106', '107'])).
% 0.52/0.76  thf('113', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | (m1_subset_1 @ 
% 0.52/0.76           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76            (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['111', '112'])).
% 0.52/0.76  thf('114', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_D @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(redefinition_k3_funct_2, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.52/0.76         ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.76         ( m1_subset_1 @ D @ A ) ) =>
% 0.52/0.76       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.52/0.76  thf('115', plain,
% 0.52/0.76      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.52/0.76          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.52/0.76          | ~ (v1_funct_1 @ X21)
% 0.52/0.76          | (v1_xboole_0 @ X22)
% 0.52/0.76          | ~ (m1_subset_1 @ X24 @ X22)
% 0.52/0.76          | ((k3_funct_2 @ X22 @ X23 @ X21 @ X24) = (k1_funct_1 @ X21 @ X24)))),
% 0.52/0.76      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.52/0.76  thf('116', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.52/0.76            X0) = (k1_funct_1 @ sk_D @ X0))
% 0.52/0.76          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.52/0.76          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['114', '115'])).
% 0.52/0.76  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('118', plain,
% 0.52/0.76      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('119', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.52/0.76            X0) = (k1_funct_1 @ sk_D @ X0))
% 0.52/0.76          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.76      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.52/0.76  thf('120', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.52/0.76            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C)))
% 0.52/0.76            = (k1_funct_1 @ sk_D @ 
% 0.52/0.76               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76                (u1_struct_0 @ sk_C)))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['113', '119'])).
% 0.52/0.76  thf('121', plain,
% 0.52/0.76      ((((k1_funct_1 @ sk_E_1 @ 
% 0.52/0.76          (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_C)))
% 0.52/0.76          = (k1_funct_1 @ sk_D @ 
% 0.52/0.76             (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76              (u1_struct_0 @ sk_C))))
% 0.52/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['110', '120'])).
% 0.52/0.76  thf('122', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | ((k1_funct_1 @ sk_E_1 @ 
% 0.52/0.76            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C)))
% 0.52/0.76            = (k1_funct_1 @ sk_D @ 
% 0.52/0.76               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76                (u1_struct_0 @ sk_C)))))),
% 0.52/0.76      inference('simplify', [status(thm)], ['121'])).
% 0.52/0.76  thf('123', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | (r2_hidden @ 
% 0.52/0.76           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76            (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76           (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['98', '99'])).
% 0.52/0.76  thf(t72_funct_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.52/0.76       ( ( r2_hidden @ A @ B ) =>
% 0.52/0.76         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.52/0.76  thf('124', plain,
% 0.52/0.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X9 @ X10)
% 0.52/0.76          | ~ (v1_relat_1 @ X11)
% 0.52/0.76          | ~ (v1_funct_1 @ X11)
% 0.52/0.76          | ((k1_funct_1 @ (k7_relat_1 @ X11 @ X10) @ X9)
% 0.52/0.76              = (k1_funct_1 @ X11 @ X9)))),
% 0.52/0.76      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.52/0.76  thf('125', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76              (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76               (u1_struct_0 @ sk_C)))
% 0.52/0.76              = (k1_funct_1 @ X0 @ 
% 0.52/0.76                 (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76                  (u1_struct_0 @ sk_C))))
% 0.52/0.76          | ~ (v1_funct_1 @ X0)
% 0.52/0.76          | ~ (v1_relat_1 @ X0))),
% 0.52/0.76      inference('sup-', [status(thm)], ['123', '124'])).
% 0.52/0.76  thf('126', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.52/0.76         (~ (v1_funct_1 @ X12)
% 0.52/0.76          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.52/0.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.52/0.76          | ((k1_funct_1 @ X15 @ (sk_E @ X12 @ X15 @ X13))
% 0.52/0.76              != (k1_funct_1 @ X12 @ (sk_E @ X12 @ X15 @ X13)))
% 0.52/0.76          | (r2_funct_2 @ X13 @ X14 @ X15 @ X12)
% 0.52/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.52/0.76          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.52/0.76          | ~ (v1_funct_1 @ X15))),
% 0.52/0.76      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.52/0.76  thf('127', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k1_funct_1 @ sk_D @ 
% 0.52/0.76            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C)))
% 0.52/0.76            != (k1_funct_1 @ sk_E_1 @ 
% 0.52/0.76                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76                 (u1_struct_0 @ sk_C))))
% 0.52/0.76          | ~ (v1_relat_1 @ sk_D)
% 0.52/0.76          | ~ (v1_funct_1 @ sk_D)
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.52/0.76          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76               (u1_struct_0 @ sk_C) @ X0)
% 0.52/0.76          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.52/0.76          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.52/0.76             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.52/0.76          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.52/0.76          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.52/0.76          | ~ (v1_funct_1 @ sk_E_1))),
% 0.52/0.76      inference('sup-', [status(thm)], ['125', '126'])).
% 0.52/0.76  thf('128', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_D @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(cc2_relat_1, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( v1_relat_1 @ A ) =>
% 0.52/0.76       ( ![B:$i]:
% 0.52/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.76  thf('129', plain,
% 0.52/0.76      (![X5 : $i, X6 : $i]:
% 0.52/0.76         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.52/0.76          | (v1_relat_1 @ X5)
% 0.52/0.76          | ~ (v1_relat_1 @ X6))),
% 0.52/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.76  thf('130', plain,
% 0.52/0.76      ((~ (v1_relat_1 @ 
% 0.52/0.76           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.52/0.76        | (v1_relat_1 @ sk_D))),
% 0.52/0.76      inference('sup-', [status(thm)], ['128', '129'])).
% 0.52/0.76  thf(fc6_relat_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.76  thf('131', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.52/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.76  thf('132', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.76      inference('demod', [status(thm)], ['130', '131'])).
% 0.52/0.76  thf('133', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('134', plain,
% 0.52/0.76      ((v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('demod', [status(thm)], ['91', '92'])).
% 0.52/0.76  thf('135', plain, ((v1_funct_1 @ sk_E_1)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('136', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k1_funct_1 @ sk_D @ 
% 0.52/0.76            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C)))
% 0.52/0.76            != (k1_funct_1 @ sk_E_1 @ 
% 0.52/0.76                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76                 (u1_struct_0 @ sk_C))))
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76               (u1_struct_0 @ sk_C) @ X0)
% 0.52/0.76          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.52/0.76          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.52/0.76             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.52/0.76          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.52/0.76          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['127', '132', '133', '134', '135'])).
% 0.52/0.76  thf('137', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (((k1_funct_1 @ sk_D @ 
% 0.52/0.76            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C)))
% 0.52/0.76            != (k1_funct_1 @ sk_D @ 
% 0.52/0.76                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76                 (u1_struct_0 @ sk_C))))
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.52/0.76          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.52/0.76          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.52/0.76             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.52/0.76          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.52/0.76          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76               (u1_struct_0 @ sk_C) @ X0)
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['122', '136'])).
% 0.52/0.76  thf('138', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C) @ X0)
% 0.52/0.76          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.52/0.76          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.52/0.76             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.52/0.76          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.52/0.76               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.52/0.76          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['137'])).
% 0.52/0.76  thf('139', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.52/0.76        | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.52/0.76             (k1_zfmisc_1 @ 
% 0.52/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.52/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.52/0.76        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['45', '138'])).
% 0.52/0.76  thf('140', plain,
% 0.52/0.76      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('141', plain,
% 0.52/0.76      ((m1_subset_1 @ sk_E_1 @ 
% 0.52/0.76        (k1_zfmisc_1 @ 
% 0.52/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('142', plain,
% 0.52/0.76      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.52/0.76        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.52/0.76      inference('demod', [status(thm)], ['71', '72'])).
% 0.52/0.76  thf('143', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.52/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1))),
% 0.52/0.76      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.52/0.76  thf('144', plain,
% 0.52/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.76          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)),
% 0.52/0.76      inference('demod', [status(thm)], ['95', '96'])).
% 0.52/0.76  thf('145', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.76      inference('clc', [status(thm)], ['143', '144'])).
% 0.52/0.76  thf(fc2_struct_0, axiom,
% 0.52/0.76    (![A:$i]:
% 0.52/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.52/0.76       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.76  thf('146', plain,
% 0.52/0.76      (![X28 : $i]:
% 0.52/0.76         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 0.52/0.76          | ~ (l1_struct_0 @ X28)
% 0.52/0.76          | (v2_struct_0 @ X28))),
% 0.52/0.76      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.52/0.76  thf('147', plain,
% 0.52/0.76      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.52/0.76        | (v2_struct_0 @ sk_C)
% 0.52/0.76        | ~ (l1_struct_0 @ sk_C))),
% 0.52/0.76      inference('sup-', [status(thm)], ['145', '146'])).
% 0.52/0.76  thf('148', plain, (~ (v2_struct_0 @ sk_C)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('149', plain,
% 0.52/0.76      ((~ (l1_struct_0 @ sk_C) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.76      inference('clc', [status(thm)], ['147', '148'])).
% 0.52/0.76  thf('150', plain,
% 0.52/0.76      ((~ (l1_pre_topc @ sk_C) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['1', '149'])).
% 0.52/0.76  thf('151', plain, ((l1_pre_topc @ sk_C)),
% 0.52/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.52/0.76  thf('152', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.52/0.76      inference('demod', [status(thm)], ['150', '151'])).
% 0.52/0.76  thf('153', plain,
% 0.52/0.76      (![X28 : $i]:
% 0.52/0.76         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 0.52/0.76          | ~ (l1_struct_0 @ X28)
% 0.52/0.76          | (v2_struct_0 @ X28))),
% 0.52/0.76      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.52/0.76  thf('154', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.52/0.76      inference('sup-', [status(thm)], ['152', '153'])).
% 0.52/0.76  thf('155', plain, (~ (v2_struct_0 @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('156', plain, (~ (l1_struct_0 @ sk_B)),
% 0.52/0.76      inference('clc', [status(thm)], ['154', '155'])).
% 0.52/0.76  thf('157', plain, (~ (l1_pre_topc @ sk_B)),
% 0.52/0.76      inference('sup-', [status(thm)], ['0', '156'])).
% 0.52/0.76  thf('158', plain, ((l1_pre_topc @ sk_B)),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('159', plain, ($false), inference('demod', [status(thm)], ['157', '158'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
