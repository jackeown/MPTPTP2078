%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y28D4lLHwp

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:38 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  188 (1473 expanded)
%              Number of leaves         :   40 ( 442 expanded)
%              Depth                    :   35
%              Number of atoms          : 2298 (58865 expanded)
%              Number of equality atoms :   33 ( 824 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( ( k2_tmap_1 @ X34 @ X32 @ X35 @ X33 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) @ X35 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X37 )
      | ~ ( l1_struct_0 @ X39 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X37 @ X38 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X11 @ X9 ) @ X9 )
      | ( r2_funct_2 @ X9 @ X10 @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X14 @ X15 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('60',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('64',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X37 )
      | ~ ( l1_struct_0 @ X39 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X37 @ X38 @ X36 @ X39 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['63','77'])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('81',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['61','81'])).

thf('83',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('85',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['82','85'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X40 )
        = ( k1_funct_1 @ sk_E_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['82','85'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('93',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['90','101'])).

thf('103',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('104',plain,(
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

thf('105',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ X22 )
      | ( ( k3_funct_2 @ X22 @ X23 @ X21 @ X24 )
        = ( k1_funct_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,
    ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['102','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('113',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X4 @ X3 ) @ X2 )
        = ( k1_funct_1 @ X4 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_E @ X8 @ X11 @ X9 ) )
       != ( k1_funct_1 @ X8 @ ( sk_E @ X8 @ X11 @ X9 ) ) )
      | ( r2_funct_2 @ X9 @ X10 @ X11 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('116',plain,(
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
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('118',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('119',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('122',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['116','119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['111','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','125'])).

thf('127',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['126','127','128','129'])).

thf('131',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('133',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('139',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['144','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y28D4lLHwp
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:27:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.89/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.08  % Solved by: fo/fo7.sh
% 0.89/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.08  % done 629 iterations in 0.596s
% 0.89/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.08  % SZS output start Refutation
% 0.89/1.08  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.89/1.08  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.89/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.08  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.89/1.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.08  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.89/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.08  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.89/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.89/1.08  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.89/1.08  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.08  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.89/1.08  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.89/1.08  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.89/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.08  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.89/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.08  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.89/1.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.89/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.08  thf(dt_l1_pre_topc, axiom,
% 0.89/1.08    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.89/1.08  thf('0', plain, (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.08  thf('1', plain, (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.08  thf('2', plain, (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.08  thf(t59_tmap_1, conjecture,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.89/1.08             ( l1_pre_topc @ B ) ) =>
% 0.89/1.08           ( ![C:$i]:
% 0.89/1.08             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.89/1.08               ( ![D:$i]:
% 0.89/1.08                 ( ( ( v1_funct_1 @ D ) & 
% 0.89/1.08                     ( v1_funct_2 @
% 0.89/1.08                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.89/1.08                     ( m1_subset_1 @
% 0.89/1.08                       D @ 
% 0.89/1.08                       ( k1_zfmisc_1 @
% 0.89/1.08                         ( k2_zfmisc_1 @
% 0.89/1.08                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.89/1.08                   ( ![E:$i]:
% 0.89/1.08                     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.08                         ( v1_funct_2 @
% 0.89/1.08                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.89/1.08                         ( m1_subset_1 @
% 0.89/1.08                           E @ 
% 0.89/1.08                           ( k1_zfmisc_1 @
% 0.89/1.08                             ( k2_zfmisc_1 @
% 0.89/1.08                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.89/1.08                       ( ( ![F:$i]:
% 0.89/1.08                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.89/1.08                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.89/1.08                               ( ( k3_funct_2 @
% 0.89/1.08                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.08                                   D @ F ) =
% 0.89/1.08                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.89/1.08                         ( r2_funct_2 @
% 0.89/1.08                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.08                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.08    (~( ![A:$i]:
% 0.89/1.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.89/1.08            ( l1_pre_topc @ A ) ) =>
% 0.89/1.08          ( ![B:$i]:
% 0.89/1.08            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.89/1.08                ( l1_pre_topc @ B ) ) =>
% 0.89/1.08              ( ![C:$i]:
% 0.89/1.08                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.89/1.08                  ( ![D:$i]:
% 0.89/1.08                    ( ( ( v1_funct_1 @ D ) & 
% 0.89/1.08                        ( v1_funct_2 @
% 0.89/1.08                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.89/1.08                        ( m1_subset_1 @
% 0.89/1.08                          D @ 
% 0.89/1.08                          ( k1_zfmisc_1 @
% 0.89/1.08                            ( k2_zfmisc_1 @
% 0.89/1.08                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.89/1.08                      ( ![E:$i]:
% 0.89/1.08                        ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.08                            ( v1_funct_2 @
% 0.89/1.08                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.89/1.08                            ( m1_subset_1 @
% 0.89/1.08                              E @ 
% 0.89/1.08                              ( k1_zfmisc_1 @
% 0.89/1.08                                ( k2_zfmisc_1 @
% 0.89/1.08                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.89/1.08                          ( ( ![F:$i]:
% 0.89/1.08                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.89/1.08                                ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.89/1.08                                  ( ( k3_funct_2 @
% 0.89/1.08                                      ( u1_struct_0 @ B ) @ 
% 0.89/1.08                                      ( u1_struct_0 @ A ) @ D @ F ) =
% 0.89/1.08                                    ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.89/1.08                            ( r2_funct_2 @
% 0.89/1.08                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.89/1.08                              ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) )),
% 0.89/1.08    inference('cnf.neg', [status(esa)], [t59_tmap_1])).
% 0.89/1.08  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('4', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(d4_tmap_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.89/1.08             ( l1_pre_topc @ B ) ) =>
% 0.89/1.08           ( ![C:$i]:
% 0.89/1.08             ( ( ( v1_funct_1 @ C ) & 
% 0.89/1.08                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.08                 ( m1_subset_1 @
% 0.89/1.08                   C @ 
% 0.89/1.08                   ( k1_zfmisc_1 @
% 0.89/1.08                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.89/1.08               ( ![D:$i]:
% 0.89/1.08                 ( ( m1_pre_topc @ D @ A ) =>
% 0.89/1.08                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.89/1.08                     ( k2_partfun1 @
% 0.89/1.08                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.89/1.08                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.89/1.08  thf('5', plain,
% 0.89/1.08      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.08         ((v2_struct_0 @ X32)
% 0.89/1.08          | ~ (v2_pre_topc @ X32)
% 0.89/1.08          | ~ (l1_pre_topc @ X32)
% 0.89/1.08          | ~ (m1_pre_topc @ X33 @ X34)
% 0.89/1.08          | ((k2_tmap_1 @ X34 @ X32 @ X35 @ X33)
% 0.89/1.08              = (k2_partfun1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32) @ 
% 0.89/1.08                 X35 @ (u1_struct_0 @ X33)))
% 0.89/1.08          | ~ (m1_subset_1 @ X35 @ 
% 0.89/1.08               (k1_zfmisc_1 @ 
% 0.89/1.08                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))))
% 0.89/1.08          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))
% 0.89/1.08          | ~ (v1_funct_1 @ X35)
% 0.89/1.08          | ~ (l1_pre_topc @ X34)
% 0.89/1.08          | ~ (v2_pre_topc @ X34)
% 0.89/1.08          | (v2_struct_0 @ X34))),
% 0.89/1.08      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.89/1.08  thf('6', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v2_struct_0 @ sk_B)
% 0.89/1.08          | ~ (v2_pre_topc @ sk_B)
% 0.89/1.08          | ~ (l1_pre_topc @ sk_B)
% 0.89/1.08          | ~ (v1_funct_1 @ sk_D)
% 0.89/1.08          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.89/1.08          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.89/1.08              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                 sk_D @ (u1_struct_0 @ X0)))
% 0.89/1.08          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.89/1.08          | ~ (l1_pre_topc @ sk_A)
% 0.89/1.08          | ~ (v2_pre_topc @ sk_A)
% 0.89/1.08          | (v2_struct_0 @ sk_A))),
% 0.89/1.08      inference('sup-', [status(thm)], ['4', '5'])).
% 0.89/1.08  thf('7', plain, ((v2_pre_topc @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('10', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('11', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(redefinition_k2_partfun1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.08     ( ( ( v1_funct_1 @ C ) & 
% 0.89/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.08       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.89/1.08  thf('12', plain,
% 0.89/1.08      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.89/1.08          | ~ (v1_funct_1 @ X17)
% 0.89/1.08          | ((k2_partfun1 @ X18 @ X19 @ X17 @ X20) = (k7_relat_1 @ X17 @ X20)))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.89/1.08  thf('13', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.89/1.08          | ~ (v1_funct_1 @ sk_D))),
% 0.89/1.08      inference('sup-', [status(thm)], ['11', '12'])).
% 0.89/1.08  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('15', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.08  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('18', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v2_struct_0 @ sk_B)
% 0.89/1.08          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.89/1.08              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.89/1.08          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.89/1.08          | (v2_struct_0 @ sk_A))),
% 0.89/1.08      inference('demod', [status(thm)],
% 0.89/1.08                ['6', '7', '8', '9', '10', '15', '16', '17'])).
% 0.89/1.08  thf('19', plain,
% 0.89/1.08      (((v2_struct_0 @ sk_A)
% 0.89/1.08        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.89/1.08            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.89/1.08        | (v2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup-', [status(thm)], ['3', '18'])).
% 0.89/1.08  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('21', plain,
% 0.89/1.08      (((v2_struct_0 @ sk_B)
% 0.89/1.08        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.89/1.08            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.89/1.08      inference('clc', [status(thm)], ['19', '20'])).
% 0.89/1.08  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('23', plain,
% 0.89/1.08      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.89/1.08         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.89/1.08      inference('clc', [status(thm)], ['21', '22'])).
% 0.89/1.08  thf('24', plain,
% 0.89/1.08      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.08  thf('25', plain,
% 0.89/1.08      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.08  thf('26', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(dt_k2_tmap_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.08     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.89/1.08         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.89/1.08         ( m1_subset_1 @
% 0.89/1.08           C @ 
% 0.89/1.08           ( k1_zfmisc_1 @
% 0.89/1.08             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.89/1.08         ( l1_struct_0 @ D ) ) =>
% 0.89/1.08       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.89/1.08         ( v1_funct_2 @
% 0.89/1.08           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.89/1.08           ( u1_struct_0 @ B ) ) & 
% 0.89/1.08         ( m1_subset_1 @
% 0.89/1.08           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.89/1.08           ( k1_zfmisc_1 @
% 0.89/1.08             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.89/1.08  thf('27', plain,
% 0.89/1.08      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X36 @ 
% 0.89/1.08             (k1_zfmisc_1 @ 
% 0.89/1.08              (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 0.89/1.08          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 0.89/1.08          | ~ (v1_funct_1 @ X36)
% 0.89/1.08          | ~ (l1_struct_0 @ X38)
% 0.89/1.08          | ~ (l1_struct_0 @ X37)
% 0.89/1.08          | ~ (l1_struct_0 @ X39)
% 0.89/1.08          | (m1_subset_1 @ (k2_tmap_1 @ X37 @ X38 @ X36 @ X39) @ 
% 0.89/1.08             (k1_zfmisc_1 @ 
% 0.89/1.08              (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38)))))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.89/1.08  thf('28', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08           (k1_zfmisc_1 @ 
% 0.89/1.08            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_B)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_A)
% 0.89/1.08          | ~ (v1_funct_1 @ sk_D)
% 0.89/1.08          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['26', '27'])).
% 0.89/1.08  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('30', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('31', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08           (k1_zfmisc_1 @ 
% 0.89/1.08            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_B)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.08      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.89/1.08  thf('32', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (l1_pre_topc @ sk_B)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_A)
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08             (k1_zfmisc_1 @ 
% 0.89/1.08              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['25', '31'])).
% 0.89/1.08  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('34', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (l1_struct_0 @ sk_A)
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08             (k1_zfmisc_1 @ 
% 0.89/1.08              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 0.89/1.08      inference('demod', [status(thm)], ['32', '33'])).
% 0.89/1.08  thf('35', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (l1_pre_topc @ sk_A)
% 0.89/1.08          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08             (k1_zfmisc_1 @ 
% 0.89/1.08              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08          | ~ (l1_struct_0 @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['24', '34'])).
% 0.89/1.08  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('37', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08           (k1_zfmisc_1 @ 
% 0.89/1.08            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08          | ~ (l1_struct_0 @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['35', '36'])).
% 0.89/1.08  thf('38', plain,
% 0.89/1.08      (((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (k1_zfmisc_1 @ 
% 0.89/1.08          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_C))),
% 0.89/1.08      inference('sup+', [status(thm)], ['23', '37'])).
% 0.89/1.08  thf('39', plain,
% 0.89/1.08      ((~ (l1_pre_topc @ sk_C)
% 0.89/1.08        | (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08           (k1_zfmisc_1 @ 
% 0.89/1.08            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['2', '38'])).
% 0.89/1.08  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(dt_m1_pre_topc, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( l1_pre_topc @ A ) =>
% 0.89/1.08       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.89/1.08  thf('41', plain,
% 0.89/1.08      (![X26 : $i, X27 : $i]:
% 0.89/1.08         (~ (m1_pre_topc @ X26 @ X27)
% 0.89/1.08          | (l1_pre_topc @ X26)
% 0.89/1.08          | ~ (l1_pre_topc @ X27))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.89/1.08  thf('42', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.89/1.08      inference('sup-', [status(thm)], ['40', '41'])).
% 0.89/1.08  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.08      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.08  thf('45', plain,
% 0.89/1.08      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('demod', [status(thm)], ['39', '44'])).
% 0.89/1.08  thf('46', plain,
% 0.89/1.08      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('demod', [status(thm)], ['39', '44'])).
% 0.89/1.08  thf('47', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_E_1 @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(d9_funct_2, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.08       ( ![D:$i]:
% 0.89/1.08         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.89/1.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.08           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 0.89/1.08             ( ![E:$i]:
% 0.89/1.08               ( ( m1_subset_1 @ E @ A ) =>
% 0.89/1.08                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 0.89/1.08  thf('48', plain,
% 0.89/1.08      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.08         (~ (v1_funct_1 @ X8)
% 0.89/1.08          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 0.89/1.08          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.89/1.08          | (m1_subset_1 @ (sk_E @ X8 @ X11 @ X9) @ X9)
% 0.89/1.08          | (r2_funct_2 @ X9 @ X10 @ X11 @ X8)
% 0.89/1.08          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.89/1.08          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.89/1.08          | ~ (v1_funct_1 @ X11))),
% 0.89/1.08      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.89/1.08  thf('49', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (v1_funct_1 @ X0)
% 0.89/1.08          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.89/1.08          | ~ (m1_subset_1 @ X0 @ 
% 0.89/1.08               (k1_zfmisc_1 @ 
% 0.89/1.08                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.89/1.08             sk_E_1)
% 0.89/1.08          | (m1_subset_1 @ (sk_E @ sk_E_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C))
% 0.89/1.08          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.89/1.08               (u1_struct_0 @ sk_A))
% 0.89/1.08          | ~ (v1_funct_1 @ sk_E_1))),
% 0.89/1.08      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.08  thf('50', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('51', plain, ((v1_funct_1 @ sk_E_1)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('52', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (v1_funct_1 @ X0)
% 0.89/1.08          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.89/1.08          | ~ (m1_subset_1 @ X0 @ 
% 0.89/1.08               (k1_zfmisc_1 @ 
% 0.89/1.08                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.89/1.08             sk_E_1)
% 0.89/1.08          | (m1_subset_1 @ (sk_E @ sk_E_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C)))),
% 0.89/1.08      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.89/1.08  thf('53', plain,
% 0.89/1.08      (((m1_subset_1 @ 
% 0.89/1.08         (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08          (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (u1_struct_0 @ sk_C))
% 0.89/1.08        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.89/1.08        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.89/1.08        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['46', '52'])).
% 0.89/1.08  thf('54', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(dt_k2_partfun1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.08     ( ( ( v1_funct_1 @ C ) & 
% 0.89/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.08       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.89/1.08         ( m1_subset_1 @
% 0.89/1.08           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.89/1.08           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.89/1.08  thf('55', plain,
% 0.89/1.08      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.89/1.08          | ~ (v1_funct_1 @ X13)
% 0.89/1.08          | (v1_funct_1 @ (k2_partfun1 @ X14 @ X15 @ X13 @ X16)))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.89/1.08  thf('56', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v1_funct_1 @ 
% 0.89/1.08           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08            X0))
% 0.89/1.08          | ~ (v1_funct_1 @ sk_D))),
% 0.89/1.08      inference('sup-', [status(thm)], ['54', '55'])).
% 0.89/1.08  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('58', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (v1_funct_1 @ 
% 0.89/1.08          (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08           X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.08  thf('59', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['13', '14'])).
% 0.89/1.08  thf('60', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['58', '59'])).
% 0.89/1.08  thf('61', plain,
% 0.89/1.08      (((m1_subset_1 @ 
% 0.89/1.08         (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08          (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (u1_struct_0 @ sk_C))
% 0.89/1.08        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.89/1.08        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('demod', [status(thm)], ['53', '60'])).
% 0.89/1.08  thf('62', plain,
% 0.89/1.08      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.08  thf('63', plain,
% 0.89/1.08      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.89/1.08         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.89/1.08      inference('clc', [status(thm)], ['21', '22'])).
% 0.89/1.08  thf('64', plain,
% 0.89/1.08      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.08  thf('65', plain,
% 0.89/1.08      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.08  thf('66', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('67', plain,
% 0.89/1.08      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X36 @ 
% 0.89/1.08             (k1_zfmisc_1 @ 
% 0.89/1.08              (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 0.89/1.08          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 0.89/1.08          | ~ (v1_funct_1 @ X36)
% 0.89/1.08          | ~ (l1_struct_0 @ X38)
% 0.89/1.08          | ~ (l1_struct_0 @ X37)
% 0.89/1.08          | ~ (l1_struct_0 @ X39)
% 0.89/1.08          | (v1_funct_2 @ (k2_tmap_1 @ X37 @ X38 @ X36 @ X39) @ 
% 0.89/1.08             (u1_struct_0 @ X39) @ (u1_struct_0 @ X38)))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.89/1.08  thf('68', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_B)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_A)
% 0.89/1.08          | ~ (v1_funct_1 @ sk_D)
% 0.89/1.08          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['66', '67'])).
% 0.89/1.08  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('70', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('71', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_B)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_A))),
% 0.89/1.08      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.89/1.08  thf('72', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (l1_pre_topc @ sk_B)
% 0.89/1.08          | ~ (l1_struct_0 @ sk_A)
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['65', '71'])).
% 0.89/1.08  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('74', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (l1_struct_0 @ sk_A)
% 0.89/1.08          | ~ (l1_struct_0 @ X0)
% 0.89/1.08          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('demod', [status(thm)], ['72', '73'])).
% 0.89/1.08  thf('75', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (l1_pre_topc @ sk_A)
% 0.89/1.08          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.89/1.08          | ~ (l1_struct_0 @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['64', '74'])).
% 0.89/1.08  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('77', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.89/1.08           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.89/1.08          | ~ (l1_struct_0 @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['75', '76'])).
% 0.89/1.08  thf('78', plain,
% 0.89/1.08      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.89/1.08        | ~ (l1_struct_0 @ sk_C))),
% 0.89/1.08      inference('sup+', [status(thm)], ['63', '77'])).
% 0.89/1.08  thf('79', plain,
% 0.89/1.08      ((~ (l1_pre_topc @ sk_C)
% 0.89/1.08        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['62', '78'])).
% 0.89/1.08  thf('80', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.08      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.08  thf('81', plain,
% 0.89/1.08      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.89/1.08      inference('demod', [status(thm)], ['79', '80'])).
% 0.89/1.08  thf('82', plain,
% 0.89/1.08      (((m1_subset_1 @ 
% 0.89/1.08         (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08          (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (u1_struct_0 @ sk_C))
% 0.89/1.08        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1))),
% 0.89/1.08      inference('demod', [status(thm)], ['61', '81'])).
% 0.89/1.08  thf('83', plain,
% 0.89/1.08      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E_1)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('84', plain,
% 0.89/1.08      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.89/1.08         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.89/1.08      inference('clc', [status(thm)], ['21', '22'])).
% 0.89/1.08  thf('85', plain,
% 0.89/1.08      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)),
% 0.89/1.08      inference('demod', [status(thm)], ['83', '84'])).
% 0.89/1.08  thf('86', plain,
% 0.89/1.08      ((m1_subset_1 @ 
% 0.89/1.08        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08        (u1_struct_0 @ sk_C))),
% 0.89/1.08      inference('clc', [status(thm)], ['82', '85'])).
% 0.89/1.08  thf(t2_subset, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ A @ B ) =>
% 0.89/1.08       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.89/1.08  thf('87', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((r2_hidden @ X0 @ X1)
% 0.89/1.08          | (v1_xboole_0 @ X1)
% 0.89/1.08          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.89/1.08      inference('cnf', [status(esa)], [t2_subset])).
% 0.89/1.08  thf('88', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08        | (r2_hidden @ 
% 0.89/1.08           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08            (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08           (u1_struct_0 @ sk_C)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['86', '87'])).
% 0.89/1.08  thf('89', plain,
% 0.89/1.08      (![X40 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X40 @ (u1_struct_0 @ sk_C))
% 0.89/1.08          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08              sk_D @ X40) = (k1_funct_1 @ sk_E_1 @ X40))
% 0.89/1.08          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ sk_B)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('90', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08        | ~ (m1_subset_1 @ 
% 0.89/1.08             (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08              (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_B))
% 0.89/1.08        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C)))
% 0.89/1.08            = (k1_funct_1 @ sk_E_1 @ 
% 0.89/1.08               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08                (u1_struct_0 @ sk_C)))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['88', '89'])).
% 0.89/1.08  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('92', plain,
% 0.89/1.08      ((m1_subset_1 @ 
% 0.89/1.08        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08        (u1_struct_0 @ sk_C))),
% 0.89/1.08      inference('clc', [status(thm)], ['82', '85'])).
% 0.89/1.08  thf(t55_pre_topc, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.89/1.08           ( ![C:$i]:
% 0.89/1.08             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.89/1.08               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.89/1.08  thf('93', plain,
% 0.89/1.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.89/1.08         ((v2_struct_0 @ X29)
% 0.89/1.08          | ~ (m1_pre_topc @ X29 @ X30)
% 0.89/1.08          | (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.89/1.08          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.89/1.08          | ~ (l1_pre_topc @ X30)
% 0.89/1.08          | (v2_struct_0 @ X30))),
% 0.89/1.08      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.89/1.08  thf('94', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v2_struct_0 @ X0)
% 0.89/1.08          | ~ (l1_pre_topc @ X0)
% 0.89/1.08          | (m1_subset_1 @ 
% 0.89/1.08             (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08              (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ X0))
% 0.89/1.08          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.89/1.08          | (v2_struct_0 @ sk_C))),
% 0.89/1.08      inference('sup-', [status(thm)], ['92', '93'])).
% 0.89/1.08  thf('95', plain,
% 0.89/1.08      (((v2_struct_0 @ sk_C)
% 0.89/1.08        | (m1_subset_1 @ 
% 0.89/1.08           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08            (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08           (u1_struct_0 @ sk_B))
% 0.89/1.08        | ~ (l1_pre_topc @ sk_B)
% 0.89/1.08        | (v2_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup-', [status(thm)], ['91', '94'])).
% 0.89/1.08  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('97', plain,
% 0.89/1.08      (((v2_struct_0 @ sk_C)
% 0.89/1.08        | (m1_subset_1 @ 
% 0.89/1.08           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08            (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08           (u1_struct_0 @ sk_B))
% 0.89/1.08        | (v2_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['95', '96'])).
% 0.89/1.08  thf('98', plain, (~ (v2_struct_0 @ sk_C)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('99', plain,
% 0.89/1.08      (((v2_struct_0 @ sk_B)
% 0.89/1.08        | (m1_subset_1 @ 
% 0.89/1.08           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08            (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08           (u1_struct_0 @ sk_B)))),
% 0.89/1.08      inference('clc', [status(thm)], ['97', '98'])).
% 0.89/1.08  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('101', plain,
% 0.89/1.08      ((m1_subset_1 @ 
% 0.89/1.08        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08        (u1_struct_0 @ sk_B))),
% 0.89/1.08      inference('clc', [status(thm)], ['99', '100'])).
% 0.89/1.08  thf('102', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C)))
% 0.89/1.08            = (k1_funct_1 @ sk_E_1 @ 
% 0.89/1.08               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08                (u1_struct_0 @ sk_C)))))),
% 0.89/1.08      inference('demod', [status(thm)], ['90', '101'])).
% 0.89/1.08  thf('103', plain,
% 0.89/1.08      ((m1_subset_1 @ 
% 0.89/1.08        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08         (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08        (u1_struct_0 @ sk_B))),
% 0.89/1.08      inference('clc', [status(thm)], ['99', '100'])).
% 0.89/1.08  thf('104', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(redefinition_k3_funct_2, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.08     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.89/1.08         ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.08         ( m1_subset_1 @ D @ A ) ) =>
% 0.89/1.08       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.89/1.08  thf('105', plain,
% 0.89/1.08      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.89/1.08          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.89/1.08          | ~ (v1_funct_1 @ X21)
% 0.89/1.08          | (v1_xboole_0 @ X22)
% 0.89/1.08          | ~ (m1_subset_1 @ X24 @ X22)
% 0.89/1.08          | ((k3_funct_2 @ X22 @ X23 @ X21 @ X24) = (k1_funct_1 @ X21 @ X24)))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.89/1.08  thf('106', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08            X0) = (k1_funct_1 @ sk_D @ X0))
% 0.89/1.08          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.89/1.08          | ~ (v1_funct_1 @ sk_D)
% 0.89/1.08          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['104', '105'])).
% 0.89/1.08  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('108', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('109', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08            X0) = (k1_funct_1 @ sk_D @ X0))
% 0.89/1.08          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.89/1.08      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.89/1.08  thf('110', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.89/1.08        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.89/1.08            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C)))
% 0.89/1.08            = (k1_funct_1 @ sk_D @ 
% 0.89/1.08               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08                (u1_struct_0 @ sk_C)))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['103', '109'])).
% 0.89/1.08  thf('111', plain,
% 0.89/1.08      ((((k1_funct_1 @ sk_E_1 @ 
% 0.89/1.08          (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08           (u1_struct_0 @ sk_C)))
% 0.89/1.08          = (k1_funct_1 @ sk_D @ 
% 0.89/1.08             (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08              (u1_struct_0 @ sk_C))))
% 0.89/1.08        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['102', '110'])).
% 0.89/1.08  thf('112', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08        | (r2_hidden @ 
% 0.89/1.08           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08            (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08           (u1_struct_0 @ sk_C)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['86', '87'])).
% 0.89/1.08  thf(t72_funct_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.89/1.08       ( ( r2_hidden @ A @ B ) =>
% 0.89/1.08         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.89/1.08  thf('113', plain,
% 0.89/1.08      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X2 @ X3)
% 0.89/1.08          | ~ (v1_relat_1 @ X4)
% 0.89/1.08          | ~ (v1_funct_1 @ X4)
% 0.89/1.08          | ((k1_funct_1 @ (k7_relat_1 @ X4 @ X3) @ X2)
% 0.89/1.08              = (k1_funct_1 @ X4 @ X2)))),
% 0.89/1.08      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.89/1.08  thf('114', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08              (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08               (u1_struct_0 @ sk_C)))
% 0.89/1.08              = (k1_funct_1 @ X0 @ 
% 0.89/1.08                 (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08                  (u1_struct_0 @ sk_C))))
% 0.89/1.08          | ~ (v1_funct_1 @ X0)
% 0.89/1.08          | ~ (v1_relat_1 @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['112', '113'])).
% 0.89/1.08  thf('115', plain,
% 0.89/1.08      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.89/1.08         (~ (v1_funct_1 @ X8)
% 0.89/1.08          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 0.89/1.08          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.89/1.08          | ((k1_funct_1 @ X11 @ (sk_E @ X8 @ X11 @ X9))
% 0.89/1.08              != (k1_funct_1 @ X8 @ (sk_E @ X8 @ X11 @ X9)))
% 0.89/1.08          | (r2_funct_2 @ X9 @ X10 @ X11 @ X8)
% 0.89/1.08          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.89/1.08          | ~ (v1_funct_2 @ X11 @ X9 @ X10)
% 0.89/1.08          | ~ (v1_funct_1 @ X11))),
% 0.89/1.08      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.89/1.08  thf('116', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (((k1_funct_1 @ sk_D @ 
% 0.89/1.08            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C)))
% 0.89/1.08            != (k1_funct_1 @ sk_E_1 @ 
% 0.89/1.08                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08                 (u1_struct_0 @ sk_C))))
% 0.89/1.08          | ~ (v1_relat_1 @ sk_D)
% 0.89/1.08          | ~ (v1_funct_1 @ sk_D)
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.89/1.08          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08               (u1_struct_0 @ sk_C) @ X0)
% 0.89/1.08          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.89/1.08          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.89/1.08             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.89/1.08          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.89/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.89/1.08          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.89/1.08          | ~ (v1_funct_1 @ sk_E_1))),
% 0.89/1.08      inference('sup-', [status(thm)], ['114', '115'])).
% 0.89/1.08  thf('117', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(cc1_relset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( v1_relat_1 @ C ) ))).
% 0.89/1.08  thf('118', plain,
% 0.89/1.08      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.89/1.08         ((v1_relat_1 @ X5)
% 0.89/1.08          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.89/1.08      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.08  thf('119', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.08      inference('sup-', [status(thm)], ['117', '118'])).
% 0.89/1.08  thf('120', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('121', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['58', '59'])).
% 0.89/1.08  thf('122', plain, ((v1_funct_1 @ sk_E_1)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('123', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (((k1_funct_1 @ sk_D @ 
% 0.89/1.08            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C)))
% 0.89/1.08            != (k1_funct_1 @ sk_E_1 @ 
% 0.89/1.08                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08                 (u1_struct_0 @ sk_C))))
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08               (u1_struct_0 @ sk_C) @ X0)
% 0.89/1.08          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.89/1.08          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.89/1.08             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.89/1.08          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.89/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.89/1.08          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0))),
% 0.89/1.08      inference('demod', [status(thm)], ['116', '119', '120', '121', '122'])).
% 0.89/1.08  thf('124', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (((k1_funct_1 @ sk_D @ 
% 0.89/1.08            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C)))
% 0.89/1.08            != (k1_funct_1 @ sk_D @ 
% 0.89/1.08                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08                 (u1_struct_0 @ sk_C))))
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.89/1.08          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.89/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.89/1.08          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.89/1.08             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.89/1.08          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.89/1.08          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08               (u1_struct_0 @ sk_C) @ X0)
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['111', '123'])).
% 0.89/1.08  thf('125', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C) @ X0)
% 0.89/1.08          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.89/1.08          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.89/1.08             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.89/1.08          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.89/1.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.89/1.08          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.89/1.08      inference('simplify', [status(thm)], ['124'])).
% 0.89/1.08  thf('126', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.89/1.08        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.89/1.08        | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.89/1.08             (k1_zfmisc_1 @ 
% 0.89/1.08              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.89/1.08        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.89/1.08        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['45', '125'])).
% 0.89/1.08  thf('127', plain,
% 0.89/1.08      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('128', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_E_1 @ 
% 0.89/1.08        (k1_zfmisc_1 @ 
% 0.89/1.08         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('129', plain,
% 0.89/1.08      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.89/1.08        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.89/1.08      inference('demod', [status(thm)], ['79', '80'])).
% 0.89/1.08  thf('130', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.89/1.08        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1))),
% 0.89/1.08      inference('demod', [status(thm)], ['126', '127', '128', '129'])).
% 0.89/1.08  thf('131', plain,
% 0.89/1.08      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)),
% 0.89/1.08      inference('demod', [status(thm)], ['83', '84'])).
% 0.89/1.08  thf('132', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.89/1.08        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.89/1.08      inference('clc', [status(thm)], ['130', '131'])).
% 0.89/1.08  thf(fc2_struct_0, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.89/1.08       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.89/1.08  thf('133', plain,
% 0.89/1.08      (![X28 : $i]:
% 0.89/1.08         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 0.89/1.08          | ~ (l1_struct_0 @ X28)
% 0.89/1.08          | (v2_struct_0 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.89/1.08  thf('134', plain,
% 0.89/1.08      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.89/1.08        | (v2_struct_0 @ sk_C)
% 0.89/1.08        | ~ (l1_struct_0 @ sk_C))),
% 0.89/1.08      inference('sup-', [status(thm)], ['132', '133'])).
% 0.89/1.08  thf('135', plain, (~ (v2_struct_0 @ sk_C)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('136', plain,
% 0.89/1.08      ((~ (l1_struct_0 @ sk_C) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.89/1.08      inference('clc', [status(thm)], ['134', '135'])).
% 0.89/1.08  thf('137', plain,
% 0.89/1.08      ((~ (l1_pre_topc @ sk_C) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['1', '136'])).
% 0.89/1.08  thf('138', plain, ((l1_pre_topc @ sk_C)),
% 0.89/1.08      inference('demod', [status(thm)], ['42', '43'])).
% 0.89/1.08  thf('139', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.89/1.08      inference('demod', [status(thm)], ['137', '138'])).
% 0.89/1.08  thf('140', plain,
% 0.89/1.08      (![X28 : $i]:
% 0.89/1.08         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 0.89/1.08          | ~ (l1_struct_0 @ X28)
% 0.89/1.08          | (v2_struct_0 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.89/1.08  thf('141', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.89/1.08      inference('sup-', [status(thm)], ['139', '140'])).
% 0.89/1.08  thf('142', plain, (~ (v2_struct_0 @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('143', plain, (~ (l1_struct_0 @ sk_B)),
% 0.89/1.08      inference('clc', [status(thm)], ['141', '142'])).
% 0.89/1.08  thf('144', plain, (~ (l1_pre_topc @ sk_B)),
% 0.89/1.08      inference('sup-', [status(thm)], ['0', '143'])).
% 0.89/1.08  thf('145', plain, ((l1_pre_topc @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('146', plain, ($false), inference('demod', [status(thm)], ['144', '145'])).
% 0.89/1.08  
% 0.89/1.08  % SZS output end Refutation
% 0.89/1.08  
% 0.89/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
