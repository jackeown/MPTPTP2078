%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZOqTKA8wIg

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:38 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  191 (1476 expanded)
%              Number of leaves         :   41 ( 443 expanded)
%              Depth                    :   35
%              Number of atoms          : 2314 (58881 expanded)
%              Number of equality atoms :   33 ( 824 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( ( k2_tmap_1 @ X35 @ X33 @ X36 @ X34 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) @ X36 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ( ( k2_partfun1 @ X19 @ X20 @ X18 @ X21 )
        = ( k7_relat_1 @ X18 @ X21 ) ) ) ),
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
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( l1_struct_0 @ X39 )
      | ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X40 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X38 @ X39 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) ) ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( l1_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X9 @ X12 @ X10 ) @ X10 )
      | ( r2_funct_2 @ X10 @ X11 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X15 @ X16 @ X14 @ X17 ) ) ) ),
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
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('64',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( l1_struct_0 @ X39 )
      | ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X40 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X38 @ X39 @ X37 @ X40 ) @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X39 ) ) ) ),
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
    ! [X41: $i] :
      ( ~ ( r2_hidden @ X41 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X41 )
        = ( k1_funct_1 @ sk_E_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ X23 )
      | ( ( k3_funct_2 @ X23 @ X24 @ X22 @ X25 )
        = ( k1_funct_1 @ X22 @ X25 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X8 @ X7 ) @ X6 )
        = ( k1_funct_1 @ X8 @ X6 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k1_funct_1 @ X12 @ ( sk_E @ X9 @ X12 @ X10 ) )
       != ( k1_funct_1 @ X9 @ ( sk_E @ X9 @ X12 @ X10 ) ) )
      | ( r2_funct_2 @ X10 @ X11 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X12 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X12 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('118',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('119',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('120',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('121',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('124',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_D @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['116','121','122','123','124'])).

thf('126',plain,(
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
    inference('sup-',[status(thm)],['111','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','127'])).

thf('129',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('135',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('141',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['146','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZOqTKA8wIg
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:37:49 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.37  % Number of cores: 8
% 0.23/0.37  % Python version: Python 3.6.8
% 0.23/0.37  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 664 iterations in 0.506s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.75/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.96  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.75/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.75/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.75/0.96  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.75/0.96  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.75/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.96  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.75/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.96  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/0.96  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.75/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.96  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.75/0.96  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.75/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.75/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.96  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.75/0.96  thf(dt_l1_pre_topc, axiom,
% 0.75/0.96    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.75/0.96  thf('0', plain, (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.96  thf('1', plain, (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.96  thf('2', plain, (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.96  thf(t59_tmap_1, conjecture,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.96       ( ![B:$i]:
% 0.75/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.75/0.96             ( l1_pre_topc @ B ) ) =>
% 0.75/0.96           ( ![C:$i]:
% 0.75/0.96             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.75/0.96               ( ![D:$i]:
% 0.75/0.96                 ( ( ( v1_funct_1 @ D ) & 
% 0.75/0.96                     ( v1_funct_2 @
% 0.75/0.96                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.75/0.96                     ( m1_subset_1 @
% 0.75/0.96                       D @ 
% 0.75/0.96                       ( k1_zfmisc_1 @
% 0.75/0.96                         ( k2_zfmisc_1 @
% 0.75/0.96                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.75/0.96                   ( ![E:$i]:
% 0.75/0.96                     ( ( ( v1_funct_1 @ E ) & 
% 0.75/0.96                         ( v1_funct_2 @
% 0.75/0.96                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.75/0.96                         ( m1_subset_1 @
% 0.75/0.96                           E @ 
% 0.75/0.96                           ( k1_zfmisc_1 @
% 0.75/0.96                             ( k2_zfmisc_1 @
% 0.75/0.96                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.75/0.96                       ( ( ![F:$i]:
% 0.75/0.96                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.75/0.96                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.75/0.96                               ( ( k3_funct_2 @
% 0.75/0.96                                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.96                                   D @ F ) =
% 0.75/0.96                                 ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.75/0.96                         ( r2_funct_2 @
% 0.75/0.96                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.96                           ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.96    (~( ![A:$i]:
% 0.75/0.96        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.75/0.96            ( l1_pre_topc @ A ) ) =>
% 0.75/0.96          ( ![B:$i]:
% 0.75/0.96            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.75/0.96                ( l1_pre_topc @ B ) ) =>
% 0.75/0.96              ( ![C:$i]:
% 0.75/0.96                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.75/0.96                  ( ![D:$i]:
% 0.75/0.96                    ( ( ( v1_funct_1 @ D ) & 
% 0.75/0.96                        ( v1_funct_2 @
% 0.75/0.96                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.75/0.96                        ( m1_subset_1 @
% 0.75/0.96                          D @ 
% 0.75/0.96                          ( k1_zfmisc_1 @
% 0.75/0.96                            ( k2_zfmisc_1 @
% 0.75/0.96                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.75/0.96                      ( ![E:$i]:
% 0.75/0.96                        ( ( ( v1_funct_1 @ E ) & 
% 0.75/0.96                            ( v1_funct_2 @
% 0.75/0.96                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) & 
% 0.75/0.96                            ( m1_subset_1 @
% 0.75/0.96                              E @ 
% 0.75/0.96                              ( k1_zfmisc_1 @
% 0.75/0.96                                ( k2_zfmisc_1 @
% 0.75/0.96                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.75/0.96                          ( ( ![F:$i]:
% 0.75/0.96                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.75/0.96                                ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.75/0.96                                  ( ( k3_funct_2 @
% 0.75/0.96                                      ( u1_struct_0 @ B ) @ 
% 0.75/0.96                                      ( u1_struct_0 @ A ) @ D @ F ) =
% 0.75/0.96                                    ( k1_funct_1 @ E @ F ) ) ) ) ) =>
% 0.75/0.96                            ( r2_funct_2 @
% 0.75/0.96                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.75/0.96                              ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t59_tmap_1])).
% 0.75/0.96  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(d4_tmap_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.96       ( ![B:$i]:
% 0.75/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.75/0.96             ( l1_pre_topc @ B ) ) =>
% 0.75/0.96           ( ![C:$i]:
% 0.75/0.96             ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.96                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.96                 ( m1_subset_1 @
% 0.75/0.96                   C @ 
% 0.75/0.96                   ( k1_zfmisc_1 @
% 0.75/0.96                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.75/0.96               ( ![D:$i]:
% 0.75/0.96                 ( ( m1_pre_topc @ D @ A ) =>
% 0.75/0.96                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.75/0.96                     ( k2_partfun1 @
% 0.75/0.96                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.75/0.96                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.75/0.96         ((v2_struct_0 @ X33)
% 0.75/0.96          | ~ (v2_pre_topc @ X33)
% 0.75/0.96          | ~ (l1_pre_topc @ X33)
% 0.75/0.96          | ~ (m1_pre_topc @ X34 @ X35)
% 0.75/0.96          | ((k2_tmap_1 @ X35 @ X33 @ X36 @ X34)
% 0.75/0.96              = (k2_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ 
% 0.75/0.96                 X36 @ (u1_struct_0 @ X34)))
% 0.75/0.96          | ~ (m1_subset_1 @ X36 @ 
% 0.75/0.96               (k1_zfmisc_1 @ 
% 0.75/0.96                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 0.75/0.96          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 0.75/0.96          | ~ (v1_funct_1 @ X36)
% 0.75/0.96          | ~ (l1_pre_topc @ X35)
% 0.75/0.96          | ~ (v2_pre_topc @ X35)
% 0.75/0.96          | (v2_struct_0 @ X35))),
% 0.75/0.96      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.75/0.96  thf('6', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v2_struct_0 @ sk_B)
% 0.75/0.96          | ~ (v2_pre_topc @ sk_B)
% 0.75/0.96          | ~ (l1_pre_topc @ sk_B)
% 0.75/0.96          | ~ (v1_funct_1 @ sk_D)
% 0.75/0.96          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.75/0.96          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.75/0.96              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96                 sk_D @ (u1_struct_0 @ X0)))
% 0.75/0.96          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.75/0.96          | ~ (l1_pre_topc @ sk_A)
% 0.75/0.96          | ~ (v2_pre_topc @ sk_A)
% 0.75/0.96          | (v2_struct_0 @ sk_A))),
% 0.75/0.96      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.96  thf('7', plain, ((v2_pre_topc @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('10', plain,
% 0.75/0.96      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('11', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(redefinition_k2_partfun1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.75/0.96  thf('12', plain,
% 0.75/0.96      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.75/0.96          | ~ (v1_funct_1 @ X18)
% 0.75/0.96          | ((k2_partfun1 @ X19 @ X20 @ X18 @ X21) = (k7_relat_1 @ X18 @ X21)))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.75/0.96  thf('13', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.75/0.96          | ~ (v1_funct_1 @ sk_D))),
% 0.75/0.96      inference('sup-', [status(thm)], ['11', '12'])).
% 0.75/0.96  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('15', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['13', '14'])).
% 0.75/0.96  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('18', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v2_struct_0 @ sk_B)
% 0.75/0.96          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.75/0.96              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.75/0.96          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.75/0.96          | (v2_struct_0 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)],
% 0.75/0.96                ['6', '7', '8', '9', '10', '15', '16', '17'])).
% 0.75/0.96  thf('19', plain,
% 0.75/0.96      (((v2_struct_0 @ sk_A)
% 0.75/0.96        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.75/0.96            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.75/0.96        | (v2_struct_0 @ sk_B))),
% 0.75/0.96      inference('sup-', [status(thm)], ['3', '18'])).
% 0.75/0.96  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('21', plain,
% 0.75/0.96      (((v2_struct_0 @ sk_B)
% 0.75/0.96        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.75/0.96            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.75/0.96      inference('clc', [status(thm)], ['19', '20'])).
% 0.75/0.96  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('23', plain,
% 0.75/0.96      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.75/0.96         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.75/0.96      inference('clc', [status(thm)], ['21', '22'])).
% 0.75/0.96  thf('24', plain,
% 0.75/0.96      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.96  thf('25', plain,
% 0.75/0.96      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.96  thf('26', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(dt_k2_tmap_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.75/0.96         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.75/0.96         ( m1_subset_1 @
% 0.75/0.96           C @ 
% 0.75/0.96           ( k1_zfmisc_1 @
% 0.75/0.96             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.75/0.96         ( l1_struct_0 @ D ) ) =>
% 0.75/0.96       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.75/0.96         ( v1_funct_2 @
% 0.75/0.96           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.75/0.96           ( u1_struct_0 @ B ) ) & 
% 0.75/0.96         ( m1_subset_1 @
% 0.75/0.96           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.75/0.96           ( k1_zfmisc_1 @
% 0.75/0.96             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.75/0.96  thf('27', plain,
% 0.75/0.96      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X37 @ 
% 0.75/0.96             (k1_zfmisc_1 @ 
% 0.75/0.96              (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39))))
% 0.75/0.96          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39))
% 0.75/0.96          | ~ (v1_funct_1 @ X37)
% 0.75/0.96          | ~ (l1_struct_0 @ X39)
% 0.75/0.96          | ~ (l1_struct_0 @ X38)
% 0.75/0.96          | ~ (l1_struct_0 @ X40)
% 0.75/0.96          | (m1_subset_1 @ (k2_tmap_1 @ X38 @ X39 @ X37 @ X40) @ 
% 0.75/0.96             (k1_zfmisc_1 @ 
% 0.75/0.96              (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X39)))))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.75/0.96  thf('28', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96           (k1_zfmisc_1 @ 
% 0.75/0.96            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.75/0.96          | ~ (l1_struct_0 @ X0)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_B)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_A)
% 0.75/0.96          | ~ (v1_funct_1 @ sk_D)
% 0.75/0.96          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['26', '27'])).
% 0.75/0.96  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('30', plain,
% 0.75/0.96      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('31', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96           (k1_zfmisc_1 @ 
% 0.75/0.96            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.75/0.96          | ~ (l1_struct_0 @ X0)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_B)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.75/0.96  thf('32', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (l1_pre_topc @ sk_B)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_A)
% 0.75/0.96          | ~ (l1_struct_0 @ X0)
% 0.75/0.96          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96             (k1_zfmisc_1 @ 
% 0.75/0.96              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['25', '31'])).
% 0.75/0.96  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('34', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (l1_struct_0 @ sk_A)
% 0.75/0.96          | ~ (l1_struct_0 @ X0)
% 0.75/0.96          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96             (k1_zfmisc_1 @ 
% 0.75/0.96              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))))),
% 0.75/0.96      inference('demod', [status(thm)], ['32', '33'])).
% 0.75/0.96  thf('35', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (l1_pre_topc @ sk_A)
% 0.75/0.96          | (m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96             (k1_zfmisc_1 @ 
% 0.75/0.96              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.75/0.96          | ~ (l1_struct_0 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['24', '34'])).
% 0.75/0.96  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('37', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96           (k1_zfmisc_1 @ 
% 0.75/0.96            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))))
% 0.75/0.96          | ~ (l1_struct_0 @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['35', '36'])).
% 0.75/0.96  thf('38', plain,
% 0.75/0.96      (((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (k1_zfmisc_1 @ 
% 0.75/0.96          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.75/0.96        | ~ (l1_struct_0 @ sk_C))),
% 0.75/0.96      inference('sup+', [status(thm)], ['23', '37'])).
% 0.75/0.96  thf('39', plain,
% 0.75/0.96      ((~ (l1_pre_topc @ sk_C)
% 0.75/0.96        | (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96           (k1_zfmisc_1 @ 
% 0.75/0.96            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['2', '38'])).
% 0.75/0.96  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(dt_m1_pre_topc, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( l1_pre_topc @ A ) =>
% 0.75/0.96       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.75/0.96  thf('41', plain,
% 0.75/0.96      (![X27 : $i, X28 : $i]:
% 0.75/0.96         (~ (m1_pre_topc @ X27 @ X28)
% 0.75/0.96          | (l1_pre_topc @ X27)
% 0.75/0.96          | ~ (l1_pre_topc @ X28))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.75/0.96  thf('42', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['40', '41'])).
% 0.75/0.96  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 0.75/0.96      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.96  thf('45', plain,
% 0.75/0.96      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('demod', [status(thm)], ['39', '44'])).
% 0.75/0.96  thf('46', plain,
% 0.75/0.96      ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('demod', [status(thm)], ['39', '44'])).
% 0.75/0.96  thf('47', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_E_1 @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(d9_funct_2, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96       ( ![D:$i]:
% 0.75/0.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 0.75/0.96             ( ![E:$i]:
% 0.75/0.96               ( ( m1_subset_1 @ E @ A ) =>
% 0.75/0.96                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 0.75/0.96  thf('48', plain,
% 0.75/0.96      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.96         (~ (v1_funct_1 @ X9)
% 0.75/0.96          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.75/0.96          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.75/0.96          | (m1_subset_1 @ (sk_E @ X9 @ X12 @ X10) @ X10)
% 0.75/0.96          | (r2_funct_2 @ X10 @ X11 @ X12 @ X9)
% 0.75/0.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.75/0.96          | ~ (v1_funct_2 @ X12 @ X10 @ X11)
% 0.75/0.96          | ~ (v1_funct_1 @ X12))),
% 0.75/0.96      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.75/0.96  thf('49', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_funct_1 @ X0)
% 0.75/0.96          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.96               (k1_zfmisc_1 @ 
% 0.75/0.96                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.75/0.96          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.75/0.96             sk_E_1)
% 0.75/0.96          | (m1_subset_1 @ (sk_E @ sk_E_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C))
% 0.75/0.96          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.75/0.96               (u1_struct_0 @ sk_A))
% 0.75/0.96          | ~ (v1_funct_1 @ sk_E_1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['47', '48'])).
% 0.75/0.96  thf('50', plain,
% 0.75/0.96      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('51', plain, ((v1_funct_1 @ sk_E_1)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('52', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_funct_1 @ X0)
% 0.75/0.96          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ 
% 0.75/0.96               (k1_zfmisc_1 @ 
% 0.75/0.96                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.75/0.96          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.75/0.96             sk_E_1)
% 0.75/0.96          | (m1_subset_1 @ (sk_E @ sk_E_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C)))),
% 0.75/0.96      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.75/0.96  thf('53', plain,
% 0.75/0.96      (((m1_subset_1 @ 
% 0.75/0.96         (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96          (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (u1_struct_0 @ sk_C))
% 0.75/0.96        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.75/0.96        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.75/0.96        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['46', '52'])).
% 0.75/0.96  thf('54', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(dt_k2_partfun1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.75/0.96         ( m1_subset_1 @
% 0.75/0.96           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.75/0.96           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.75/0.96  thf('55', plain,
% 0.75/0.96      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.75/0.96          | ~ (v1_funct_1 @ X14)
% 0.75/0.96          | (v1_funct_1 @ (k2_partfun1 @ X15 @ X16 @ X14 @ X17)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.75/0.96  thf('56', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v1_funct_1 @ 
% 0.75/0.96           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96            X0))
% 0.75/0.96          | ~ (v1_funct_1 @ sk_D))),
% 0.75/0.96      inference('sup-', [status(thm)], ['54', '55'])).
% 0.75/0.96  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('58', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (v1_funct_1 @ 
% 0.75/0.96          (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96           X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['56', '57'])).
% 0.75/0.96  thf('59', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['13', '14'])).
% 0.75/0.96  thf('60', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['58', '59'])).
% 0.75/0.96  thf('61', plain,
% 0.75/0.96      (((m1_subset_1 @ 
% 0.75/0.96         (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96          (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (u1_struct_0 @ sk_C))
% 0.75/0.96        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.75/0.96        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.96      inference('demod', [status(thm)], ['53', '60'])).
% 0.75/0.96  thf('62', plain,
% 0.75/0.96      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.96  thf('63', plain,
% 0.75/0.96      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.75/0.96         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.75/0.96      inference('clc', [status(thm)], ['21', '22'])).
% 0.75/0.96  thf('64', plain,
% 0.75/0.96      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.96  thf('65', plain,
% 0.75/0.96      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.75/0.96  thf('66', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('67', plain,
% 0.75/0.96      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X37 @ 
% 0.75/0.96             (k1_zfmisc_1 @ 
% 0.75/0.96              (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39))))
% 0.75/0.96          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X39))
% 0.75/0.96          | ~ (v1_funct_1 @ X37)
% 0.75/0.96          | ~ (l1_struct_0 @ X39)
% 0.75/0.96          | ~ (l1_struct_0 @ X38)
% 0.75/0.96          | ~ (l1_struct_0 @ X40)
% 0.75/0.96          | (v1_funct_2 @ (k2_tmap_1 @ X38 @ X39 @ X37 @ X40) @ 
% 0.75/0.96             (u1_struct_0 @ X40) @ (u1_struct_0 @ X39)))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.75/0.96  thf('68', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.75/0.96          | ~ (l1_struct_0 @ X0)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_B)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_A)
% 0.75/0.96          | ~ (v1_funct_1 @ sk_D)
% 0.75/0.96          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['66', '67'])).
% 0.75/0.96  thf('69', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('70', plain,
% 0.75/0.96      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('71', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.75/0.96          | ~ (l1_struct_0 @ X0)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_B)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.75/0.96  thf('72', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (l1_pre_topc @ sk_B)
% 0.75/0.96          | ~ (l1_struct_0 @ sk_A)
% 0.75/0.96          | ~ (l1_struct_0 @ X0)
% 0.75/0.96          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['65', '71'])).
% 0.75/0.96  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('74', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (l1_struct_0 @ sk_A)
% 0.75/0.96          | ~ (l1_struct_0 @ X0)
% 0.75/0.96          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.96      inference('demod', [status(thm)], ['72', '73'])).
% 0.75/0.96  thf('75', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (l1_pre_topc @ sk_A)
% 0.75/0.96          | (v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.75/0.96          | ~ (l1_struct_0 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['64', '74'])).
% 0.75/0.96  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('77', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v1_funct_2 @ (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0) @ 
% 0.75/0.96           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.75/0.96          | ~ (l1_struct_0 @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['75', '76'])).
% 0.75/0.96  thf('78', plain,
% 0.75/0.96      (((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.75/0.96        | ~ (l1_struct_0 @ sk_C))),
% 0.75/0.96      inference('sup+', [status(thm)], ['63', '77'])).
% 0.75/0.96  thf('79', plain,
% 0.75/0.96      ((~ (l1_pre_topc @ sk_C)
% 0.75/0.96        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['62', '78'])).
% 0.75/0.96  thf('80', plain, ((l1_pre_topc @ sk_C)),
% 0.75/0.96      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.96  thf('81', plain,
% 0.75/0.96      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['79', '80'])).
% 0.75/0.96  thf('82', plain,
% 0.75/0.96      (((m1_subset_1 @ 
% 0.75/0.96         (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96          (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (u1_struct_0 @ sk_C))
% 0.75/0.96        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1))),
% 0.75/0.96      inference('demod', [status(thm)], ['61', '81'])).
% 0.75/0.96  thf('83', plain,
% 0.75/0.96      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E_1)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('84', plain,
% 0.75/0.96      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.75/0.96         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.75/0.96      inference('clc', [status(thm)], ['21', '22'])).
% 0.75/0.96  thf('85', plain,
% 0.75/0.96      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)),
% 0.75/0.96      inference('demod', [status(thm)], ['83', '84'])).
% 0.75/0.96  thf('86', plain,
% 0.75/0.96      ((m1_subset_1 @ 
% 0.75/0.96        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96        (u1_struct_0 @ sk_C))),
% 0.75/0.96      inference('clc', [status(thm)], ['82', '85'])).
% 0.75/0.96  thf(t2_subset, axiom,
% 0.75/0.96    (![A:$i,B:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ A @ B ) =>
% 0.75/0.96       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.75/0.96  thf('87', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         ((r2_hidden @ X0 @ X1)
% 0.75/0.96          | (v1_xboole_0 @ X1)
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.75/0.96      inference('cnf', [status(esa)], [t2_subset])).
% 0.75/0.96  thf('88', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96        | (r2_hidden @ 
% 0.75/0.96           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96            (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96           (u1_struct_0 @ sk_C)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['86', '87'])).
% 0.75/0.96  thf('89', plain,
% 0.75/0.96      (![X41 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X41 @ (u1_struct_0 @ sk_C))
% 0.75/0.96          | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96              sk_D @ X41) = (k1_funct_1 @ sk_E_1 @ X41))
% 0.75/0.96          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('90', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96        | ~ (m1_subset_1 @ 
% 0.75/0.96             (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96              (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_B))
% 0.75/0.96        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C)))
% 0.75/0.96            = (k1_funct_1 @ sk_E_1 @ 
% 0.75/0.96               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96                (u1_struct_0 @ sk_C)))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['88', '89'])).
% 0.75/0.96  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('92', plain,
% 0.75/0.96      ((m1_subset_1 @ 
% 0.75/0.96        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96        (u1_struct_0 @ sk_C))),
% 0.75/0.96      inference('clc', [status(thm)], ['82', '85'])).
% 0.75/0.96  thf(t55_pre_topc, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.75/0.96       ( ![B:$i]:
% 0.75/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.75/0.96           ( ![C:$i]:
% 0.75/0.96             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.75/0.96               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.75/0.96  thf('93', plain,
% 0.75/0.96      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.75/0.96         ((v2_struct_0 @ X30)
% 0.75/0.96          | ~ (m1_pre_topc @ X30 @ X31)
% 0.75/0.96          | (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.75/0.96          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.75/0.96          | ~ (l1_pre_topc @ X31)
% 0.75/0.96          | (v2_struct_0 @ X31))),
% 0.75/0.96      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.75/0.96  thf('94', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v2_struct_0 @ X0)
% 0.75/0.96          | ~ (l1_pre_topc @ X0)
% 0.75/0.96          | (m1_subset_1 @ 
% 0.75/0.96             (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96              (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ X0))
% 0.75/0.96          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.75/0.96          | (v2_struct_0 @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['92', '93'])).
% 0.75/0.96  thf('95', plain,
% 0.75/0.96      (((v2_struct_0 @ sk_C)
% 0.75/0.96        | (m1_subset_1 @ 
% 0.75/0.96           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96            (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96           (u1_struct_0 @ sk_B))
% 0.75/0.96        | ~ (l1_pre_topc @ sk_B)
% 0.75/0.96        | (v2_struct_0 @ sk_B))),
% 0.75/0.96      inference('sup-', [status(thm)], ['91', '94'])).
% 0.75/0.96  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('97', plain,
% 0.75/0.96      (((v2_struct_0 @ sk_C)
% 0.75/0.96        | (m1_subset_1 @ 
% 0.75/0.96           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96            (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96           (u1_struct_0 @ sk_B))
% 0.75/0.96        | (v2_struct_0 @ sk_B))),
% 0.75/0.96      inference('demod', [status(thm)], ['95', '96'])).
% 0.75/0.96  thf('98', plain, (~ (v2_struct_0 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('99', plain,
% 0.75/0.96      (((v2_struct_0 @ sk_B)
% 0.75/0.96        | (m1_subset_1 @ 
% 0.75/0.96           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96            (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96           (u1_struct_0 @ sk_B)))),
% 0.75/0.96      inference('clc', [status(thm)], ['97', '98'])).
% 0.75/0.96  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('101', plain,
% 0.75/0.96      ((m1_subset_1 @ 
% 0.75/0.96        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96        (u1_struct_0 @ sk_B))),
% 0.75/0.96      inference('clc', [status(thm)], ['99', '100'])).
% 0.75/0.96  thf('102', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C)))
% 0.75/0.96            = (k1_funct_1 @ sk_E_1 @ 
% 0.75/0.96               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96                (u1_struct_0 @ sk_C)))))),
% 0.75/0.96      inference('demod', [status(thm)], ['90', '101'])).
% 0.75/0.96  thf('103', plain,
% 0.75/0.96      ((m1_subset_1 @ 
% 0.75/0.96        (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96         (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96        (u1_struct_0 @ sk_B))),
% 0.75/0.96      inference('clc', [status(thm)], ['99', '100'])).
% 0.75/0.96  thf('104', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(redefinition_k3_funct_2, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.75/0.96         ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.96         ( m1_subset_1 @ D @ A ) ) =>
% 0.75/0.96       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.75/0.96  thf('105', plain,
% 0.75/0.96      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.75/0.96          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.75/0.96          | ~ (v1_funct_1 @ X22)
% 0.75/0.96          | (v1_xboole_0 @ X23)
% 0.75/0.96          | ~ (m1_subset_1 @ X25 @ X23)
% 0.75/0.96          | ((k3_funct_2 @ X23 @ X24 @ X22 @ X25) = (k1_funct_1 @ X22 @ X25)))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.75/0.96  thf('106', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96            X0) = (k1_funct_1 @ sk_D @ X0))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.96          | ~ (v1_funct_1 @ sk_D)
% 0.75/0.96          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['104', '105'])).
% 0.75/0.96  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('108', plain,
% 0.75/0.96      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('109', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96            X0) = (k1_funct_1 @ sk_D @ X0))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.96      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.75/0.96  thf('110', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.96        | ((k3_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.75/0.96            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C)))
% 0.75/0.96            = (k1_funct_1 @ sk_D @ 
% 0.75/0.96               (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96                (u1_struct_0 @ sk_C)))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['103', '109'])).
% 0.75/0.96  thf('111', plain,
% 0.75/0.96      ((((k1_funct_1 @ sk_E_1 @ 
% 0.75/0.96          (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96           (u1_struct_0 @ sk_C)))
% 0.75/0.96          = (k1_funct_1 @ sk_D @ 
% 0.75/0.96             (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96              (u1_struct_0 @ sk_C))))
% 0.75/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.96      inference('sup+', [status(thm)], ['102', '110'])).
% 0.75/0.96  thf('112', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96        | (r2_hidden @ 
% 0.75/0.96           (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96            (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96           (u1_struct_0 @ sk_C)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['86', '87'])).
% 0.75/0.96  thf(t72_funct_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.75/0.96       ( ( r2_hidden @ A @ B ) =>
% 0.75/0.96         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.75/0.96  thf('113', plain,
% 0.75/0.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.75/0.96         (~ (r2_hidden @ X6 @ X7)
% 0.75/0.96          | ~ (v1_relat_1 @ X8)
% 0.75/0.96          | ~ (v1_funct_1 @ X8)
% 0.75/0.96          | ((k1_funct_1 @ (k7_relat_1 @ X8 @ X7) @ X6)
% 0.75/0.96              = (k1_funct_1 @ X8 @ X6)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.75/0.96  thf('114', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         ((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96              (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96               (u1_struct_0 @ sk_C)))
% 0.75/0.96              = (k1_funct_1 @ X0 @ 
% 0.75/0.96                 (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96                  (u1_struct_0 @ sk_C))))
% 0.75/0.96          | ~ (v1_funct_1 @ X0)
% 0.75/0.96          | ~ (v1_relat_1 @ X0))),
% 0.75/0.96      inference('sup-', [status(thm)], ['112', '113'])).
% 0.75/0.96  thf('115', plain,
% 0.75/0.96      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.75/0.96         (~ (v1_funct_1 @ X9)
% 0.75/0.96          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.75/0.96          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.75/0.96          | ((k1_funct_1 @ X12 @ (sk_E @ X9 @ X12 @ X10))
% 0.75/0.96              != (k1_funct_1 @ X9 @ (sk_E @ X9 @ X12 @ X10)))
% 0.75/0.96          | (r2_funct_2 @ X10 @ X11 @ X12 @ X9)
% 0.75/0.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.75/0.96          | ~ (v1_funct_2 @ X12 @ X10 @ X11)
% 0.75/0.96          | ~ (v1_funct_1 @ X12))),
% 0.75/0.96      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.75/0.96  thf('116', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (((k1_funct_1 @ sk_D @ 
% 0.75/0.96            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C)))
% 0.75/0.96            != (k1_funct_1 @ sk_E_1 @ 
% 0.75/0.96                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96                 (u1_struct_0 @ sk_C))))
% 0.75/0.96          | ~ (v1_relat_1 @ sk_D)
% 0.75/0.96          | ~ (v1_funct_1 @ sk_D)
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.75/0.96          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96               (u1_struct_0 @ sk_C) @ X0)
% 0.75/0.96          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.75/0.96          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.75/0.96             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.75/0.96          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.75/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.75/0.96          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.75/0.96          | ~ (v1_funct_1 @ sk_E_1))),
% 0.75/0.96      inference('sup-', [status(thm)], ['114', '115'])).
% 0.75/0.96  thf('117', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(cc2_relat_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( v1_relat_1 @ A ) =>
% 0.75/0.96       ( ![B:$i]:
% 0.75/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.75/0.96  thf('118', plain,
% 0.75/0.96      (![X2 : $i, X3 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.75/0.96          | (v1_relat_1 @ X2)
% 0.75/0.96          | ~ (v1_relat_1 @ X3))),
% 0.75/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.75/0.96  thf('119', plain,
% 0.75/0.96      ((~ (v1_relat_1 @ 
% 0.75/0.96           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.75/0.96        | (v1_relat_1 @ sk_D))),
% 0.75/0.96      inference('sup-', [status(thm)], ['117', '118'])).
% 0.75/0.96  thf(fc6_relat_1, axiom,
% 0.75/0.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.75/0.96  thf('120', plain,
% 0.75/0.96      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.75/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.75/0.96  thf('121', plain, ((v1_relat_1 @ sk_D)),
% 0.75/0.96      inference('demod', [status(thm)], ['119', '120'])).
% 0.75/0.96  thf('122', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('123', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['58', '59'])).
% 0.75/0.96  thf('124', plain, ((v1_funct_1 @ sk_E_1)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('125', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (((k1_funct_1 @ sk_D @ 
% 0.75/0.96            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C)))
% 0.75/0.96            != (k1_funct_1 @ sk_E_1 @ 
% 0.75/0.96                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96                 (u1_struct_0 @ sk_C))))
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96               (u1_struct_0 @ sk_C) @ X0)
% 0.75/0.96          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.75/0.96          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.75/0.96             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.75/0.96          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.75/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.75/0.96          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['116', '121', '122', '123', '124'])).
% 0.75/0.96  thf('126', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (((k1_funct_1 @ sk_D @ 
% 0.75/0.96            (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C)))
% 0.75/0.96            != (k1_funct_1 @ sk_D @ 
% 0.75/0.96                (sk_E @ sk_E_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96                 (u1_struct_0 @ sk_C))))
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.75/0.96          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.75/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.75/0.96          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.75/0.96             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.75/0.96          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.75/0.96          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96               (u1_struct_0 @ sk_C) @ X0)
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['111', '125'])).
% 0.75/0.96  thf('127', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C) @ X0)
% 0.75/0.96          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.75/0.96          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 0.75/0.96             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.75/0.96          | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.75/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.75/0.96          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ X0)
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96          | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['126'])).
% 0.75/0.96  thf('128', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.75/0.96        | ~ (m1_subset_1 @ sk_E_1 @ 
% 0.75/0.96             (k1_zfmisc_1 @ 
% 0.75/0.96              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.75/0.96        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)
% 0.75/0.96        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['45', '127'])).
% 0.75/0.96  thf('129', plain,
% 0.75/0.96      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('130', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_E_1 @ 
% 0.75/0.96        (k1_zfmisc_1 @ 
% 0.75/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('131', plain,
% 0.75/0.96      ((v1_funct_2 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.75/0.96        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['79', '80'])).
% 0.75/0.96  thf('132', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96           (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1))),
% 0.75/0.96      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.75/0.96  thf('133', plain,
% 0.75/0.96      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.75/0.96          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E_1)),
% 0.75/0.96      inference('demod', [status(thm)], ['83', '84'])).
% 0.75/0.96  thf('134', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.75/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.96      inference('clc', [status(thm)], ['132', '133'])).
% 0.75/0.96  thf(fc2_struct_0, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.75/0.96       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.75/0.96  thf('135', plain,
% 0.75/0.96      (![X29 : $i]:
% 0.75/0.96         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 0.75/0.96          | ~ (l1_struct_0 @ X29)
% 0.75/0.96          | (v2_struct_0 @ X29))),
% 0.75/0.96      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.75/0.96  thf('136', plain,
% 0.75/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.75/0.96        | (v2_struct_0 @ sk_C)
% 0.75/0.96        | ~ (l1_struct_0 @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['134', '135'])).
% 0.75/0.96  thf('137', plain, (~ (v2_struct_0 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('138', plain,
% 0.75/0.96      ((~ (l1_struct_0 @ sk_C) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.96      inference('clc', [status(thm)], ['136', '137'])).
% 0.75/0.96  thf('139', plain,
% 0.75/0.96      ((~ (l1_pre_topc @ sk_C) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '138'])).
% 0.75/0.96  thf('140', plain, ((l1_pre_topc @ sk_C)),
% 0.75/0.96      inference('demod', [status(thm)], ['42', '43'])).
% 0.75/0.96  thf('141', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.75/0.96      inference('demod', [status(thm)], ['139', '140'])).
% 0.75/0.96  thf('142', plain,
% 0.75/0.96      (![X29 : $i]:
% 0.75/0.96         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 0.75/0.96          | ~ (l1_struct_0 @ X29)
% 0.75/0.96          | (v2_struct_0 @ X29))),
% 0.75/0.96      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.75/0.96  thf('143', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.75/0.96      inference('sup-', [status(thm)], ['141', '142'])).
% 0.75/0.96  thf('144', plain, (~ (v2_struct_0 @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('145', plain, (~ (l1_struct_0 @ sk_B)),
% 0.75/0.96      inference('clc', [status(thm)], ['143', '144'])).
% 0.75/0.96  thf('146', plain, (~ (l1_pre_topc @ sk_B)),
% 0.75/0.96      inference('sup-', [status(thm)], ['0', '145'])).
% 0.75/0.96  thf('147', plain, ((l1_pre_topc @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('148', plain, ($false), inference('demod', [status(thm)], ['146', '147'])).
% 0.75/0.96  
% 0.75/0.96  % SZS output end Refutation
% 0.75/0.96  
% 0.75/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
