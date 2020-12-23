%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.An0VtYcNv9

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:00 EST 2020

% Result     : Theorem 6.33s
% Output     : Refutation 6.40s
% Verified   : 
% Statistics : Number of formulae       :  235 (2234 expanded)
%              Number of leaves         :   43 ( 663 expanded)
%              Depth                    :   31
%              Number of atoms          : 2796 (97082 expanded)
%              Number of equality atoms :   43 (1193 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(t73_tmap_1,conjecture,(
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
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ( ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) )
                                   => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G )
                                      = ( k1_funct_1 @ F @ G ) ) ) )
                             => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ! [G: $i] :
                                    ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                   => ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) )
                                     => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G )
                                        = ( k1_funct_1 @ F @ G ) ) ) )
                               => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X45: $i] :
      ( ( m1_pre_topc @ X45 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('3',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X39 @ X41 @ X40 @ X38 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X41 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('18',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','16','17','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X45: $i] :
      ( ( m1_pre_topc @ X45 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('32',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( k3_tmap_1 @ A @ B @ C @ D @ E )
                          = ( k2_partfun1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ~ ( m1_pre_topc @ X34 @ X36 )
      | ( ( k3_tmap_1 @ X35 @ X33 @ X36 @ X34 @ X37 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X33 ) @ X37 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E_1 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k2_partfun1 @ X20 @ X21 @ X19 @ X22 )
        = ( k7_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ X0 )
        = ( k7_relat_1 @ sk_E_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ X0 )
      = ( k7_relat_1 @ sk_E_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E_1 )
        = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 )
        = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('47',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('48',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 )
        = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 )
        = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 )
      = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 )
      = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 )
    = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','55'])).

thf('58',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('59',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X14 @ X17 @ X15 ) @ X15 )
      | ( r2_funct_2 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 @ sk_F )
      | ( m1_subset_1 @ ( sk_E @ sk_F @ X0 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ X0 @ sk_F )
      | ( m1_subset_1 @ ( sk_E @ sk_F @ X0 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X45: $i] :
      ( ( m1_pre_topc @ X45 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('67',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X39 @ X41 @ X40 @ X38 @ X42 ) @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('77',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('78',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 )
    = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('86',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X45: $i] :
      ( ( m1_pre_topc @ X45 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('89',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X39 @ X41 @ X40 @ X38 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('99',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('100',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1 ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100'])).

thf('102',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1 )
    = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('108',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['64','86','108'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('111',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1 ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E_1 )
        = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36','41','42','43'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E_1 )
        = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E_1 )
        = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1 )
      = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1 )
      = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1 )
      = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1 )
    = ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['112','126'])).

thf('128',plain,
    ( ( r2_hidden @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['111','127'])).

thf('129',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ X46 )
        = ( k1_funct_1 @ sk_F @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('131',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X43 @ X44 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf('134',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('135',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X46: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ X46 )
        = ( k1_funct_1 @ sk_F @ X46 ) )
      | ~ ( r2_hidden @ X46 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['129','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_F @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['128','137'])).

thf('139',plain,
    ( ( r2_hidden @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['111','127'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('141',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('143',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ X24 )
      | ( ( k3_funct_2 @ X24 @ X25 @ X23 @ X26 )
        = ( k1_funct_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ X0 )
        = ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ X0 )
        = ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['141','147'])).

thf('149',plain,
    ( ( ( k1_funct_1 @ sk_F @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['138','148'])).

thf('150',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( ( k1_funct_1 @ sk_F @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( r2_hidden @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['111','127'])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('152',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X10 @ X9 ) @ X8 )
        = ( k1_funct_1 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
        = ( k1_funct_1 @ X0 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( ( k1_funct_1 @ X17 @ ( sk_E @ X14 @ X17 @ X15 ) )
       != ( k1_funct_1 @ X14 @ ( sk_E @ X14 @ X17 @ X15 ) ) )
      | ( r2_funct_2 @ X15 @ X16 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_F @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ sk_E_1 )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('157',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('158',plain,(
    v1_relat_1 @ sk_E_1 ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('161',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_F @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['155','158','159','160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) )
       != ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_F @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['150','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ X0 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','164'])).

thf('166',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('169',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['112','126'])).

thf('171',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('172',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['14','15'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('175',plain,(
    ! [X29: $i] :
      ( ( l1_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('176',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['173','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('181',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('184',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X29: $i] :
      ( ( l1_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('188',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v2_struct_0 @ sk_C ),
    inference(demod,[status(thm)],['181','188'])).

thf('190',plain,(
    $false ),
    inference(demod,[status(thm)],['0','189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.An0VtYcNv9
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.33/6.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.33/6.57  % Solved by: fo/fo7.sh
% 6.33/6.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.33/6.57  % done 6803 iterations in 6.125s
% 6.33/6.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.33/6.57  % SZS output start Refutation
% 6.33/6.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.33/6.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.33/6.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.33/6.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 6.33/6.57  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 6.33/6.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.33/6.57  thf(sk_C_type, type, sk_C: $i).
% 6.33/6.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.33/6.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.33/6.57  thf(sk_B_type, type, sk_B: $i).
% 6.33/6.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.33/6.57  thf(sk_A_type, type, sk_A: $i).
% 6.33/6.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.33/6.57  thf(sk_D_type, type, sk_D: $i).
% 6.33/6.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.33/6.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.33/6.57  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 6.33/6.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.33/6.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.33/6.57  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 6.33/6.57  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 6.33/6.57  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 6.33/6.57  thf(sk_F_type, type, sk_F: $i).
% 6.33/6.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.33/6.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.33/6.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.33/6.57  thf(sk_E_1_type, type, sk_E_1: $i).
% 6.33/6.57  thf(t73_tmap_1, conjecture,
% 6.33/6.57    (![A:$i]:
% 6.33/6.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.33/6.57       ( ![B:$i]:
% 6.33/6.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.33/6.57             ( l1_pre_topc @ B ) ) =>
% 6.33/6.57           ( ![C:$i]:
% 6.33/6.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.33/6.57               ( ![D:$i]:
% 6.33/6.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.33/6.57                   ( ![E:$i]:
% 6.33/6.57                     ( ( ( v1_funct_1 @ E ) & 
% 6.33/6.57                         ( v1_funct_2 @
% 6.33/6.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 6.33/6.57                         ( m1_subset_1 @
% 6.33/6.57                           E @ 
% 6.33/6.57                           ( k1_zfmisc_1 @
% 6.33/6.57                             ( k2_zfmisc_1 @
% 6.33/6.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.33/6.57                       ( ( m1_pre_topc @ C @ D ) =>
% 6.33/6.57                         ( ![F:$i]:
% 6.33/6.57                           ( ( ( v1_funct_1 @ F ) & 
% 6.33/6.57                               ( v1_funct_2 @
% 6.33/6.57                                 F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.33/6.57                               ( m1_subset_1 @
% 6.33/6.57                                 F @ 
% 6.33/6.57                                 ( k1_zfmisc_1 @
% 6.33/6.57                                   ( k2_zfmisc_1 @
% 6.33/6.57                                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.33/6.57                             ( ( ![G:$i]:
% 6.33/6.57                                 ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 6.33/6.57                                   ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) ) =>
% 6.33/6.57                                     ( ( k3_funct_2 @
% 6.33/6.57                                         ( u1_struct_0 @ D ) @ 
% 6.33/6.57                                         ( u1_struct_0 @ B ) @ E @ G ) =
% 6.33/6.57                                       ( k1_funct_1 @ F @ G ) ) ) ) ) =>
% 6.33/6.57                               ( r2_funct_2 @
% 6.33/6.57                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 6.33/6.57                                 ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.33/6.57  thf(zf_stmt_0, negated_conjecture,
% 6.33/6.57    (~( ![A:$i]:
% 6.33/6.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.33/6.57            ( l1_pre_topc @ A ) ) =>
% 6.33/6.57          ( ![B:$i]:
% 6.33/6.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.33/6.57                ( l1_pre_topc @ B ) ) =>
% 6.33/6.57              ( ![C:$i]:
% 6.33/6.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.33/6.57                  ( ![D:$i]:
% 6.33/6.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.33/6.57                      ( ![E:$i]:
% 6.33/6.57                        ( ( ( v1_funct_1 @ E ) & 
% 6.33/6.57                            ( v1_funct_2 @
% 6.33/6.57                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 6.33/6.57                            ( m1_subset_1 @
% 6.33/6.57                              E @ 
% 6.33/6.57                              ( k1_zfmisc_1 @
% 6.33/6.57                                ( k2_zfmisc_1 @
% 6.33/6.57                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.33/6.57                          ( ( m1_pre_topc @ C @ D ) =>
% 6.33/6.57                            ( ![F:$i]:
% 6.33/6.57                              ( ( ( v1_funct_1 @ F ) & 
% 6.33/6.57                                  ( v1_funct_2 @
% 6.33/6.57                                    F @ ( u1_struct_0 @ C ) @ 
% 6.33/6.57                                    ( u1_struct_0 @ B ) ) & 
% 6.33/6.57                                  ( m1_subset_1 @
% 6.33/6.57                                    F @ 
% 6.33/6.57                                    ( k1_zfmisc_1 @
% 6.33/6.57                                      ( k2_zfmisc_1 @
% 6.33/6.57                                        ( u1_struct_0 @ C ) @ 
% 6.33/6.57                                        ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.33/6.57                                ( ( ![G:$i]:
% 6.33/6.57                                    ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 6.33/6.57                                      ( ( r2_hidden @ G @ ( u1_struct_0 @ C ) ) =>
% 6.33/6.57                                        ( ( k3_funct_2 @
% 6.33/6.57                                            ( u1_struct_0 @ D ) @ 
% 6.33/6.57                                            ( u1_struct_0 @ B ) @ E @ G ) =
% 6.33/6.57                                          ( k1_funct_1 @ F @ G ) ) ) ) ) =>
% 6.33/6.57                                  ( r2_funct_2 @
% 6.33/6.57                                    ( u1_struct_0 @ C ) @ 
% 6.33/6.57                                    ( u1_struct_0 @ B ) @ 
% 6.33/6.57                                    ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 6.33/6.57    inference('cnf.neg', [status(esa)], [t73_tmap_1])).
% 6.33/6.57  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(t2_tsep_1, axiom,
% 6.33/6.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 6.33/6.57  thf('2', plain,
% 6.33/6.57      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 6.33/6.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.33/6.57  thf('3', plain,
% 6.33/6.57      ((m1_subset_1 @ sk_E_1 @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(dt_k3_tmap_1, axiom,
% 6.33/6.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.33/6.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.33/6.57         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 6.33/6.57         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 6.33/6.57         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 6.33/6.57         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.33/6.57         ( m1_subset_1 @
% 6.33/6.57           E @ 
% 6.33/6.57           ( k1_zfmisc_1 @
% 6.33/6.57             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.33/6.57       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 6.33/6.57         ( v1_funct_2 @
% 6.33/6.57           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 6.33/6.57           ( u1_struct_0 @ B ) ) & 
% 6.33/6.57         ( m1_subset_1 @
% 6.33/6.57           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 6.33/6.57           ( k1_zfmisc_1 @
% 6.33/6.57             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 6.33/6.57  thf('4', plain,
% 6.33/6.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X38 @ X39)
% 6.33/6.57          | ~ (m1_pre_topc @ X40 @ X39)
% 6.33/6.57          | ~ (l1_pre_topc @ X41)
% 6.33/6.57          | ~ (v2_pre_topc @ X41)
% 6.33/6.57          | (v2_struct_0 @ X41)
% 6.33/6.57          | ~ (l1_pre_topc @ X39)
% 6.33/6.57          | ~ (v2_pre_topc @ X39)
% 6.33/6.57          | (v2_struct_0 @ X39)
% 6.33/6.57          | ~ (v1_funct_1 @ X42)
% 6.33/6.57          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X41))
% 6.33/6.57          | ~ (m1_subset_1 @ X42 @ 
% 6.33/6.57               (k1_zfmisc_1 @ 
% 6.33/6.57                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X41))))
% 6.33/6.57          | (m1_subset_1 @ (k3_tmap_1 @ X39 @ X41 @ X40 @ X38 @ X42) @ 
% 6.33/6.57             (k1_zfmisc_1 @ 
% 6.33/6.57              (k2_zfmisc_1 @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X41)))))),
% 6.33/6.57      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.33/6.57  thf('5', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1) @ 
% 6.33/6.57           (k1_zfmisc_1 @ 
% 6.33/6.57            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 6.33/6.57          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ 
% 6.33/6.57               (u1_struct_0 @ sk_B))
% 6.33/6.57          | ~ (v1_funct_1 @ sk_E_1)
% 6.33/6.57          | (v2_struct_0 @ X1)
% 6.33/6.57          | ~ (v2_pre_topc @ X1)
% 6.33/6.57          | ~ (l1_pre_topc @ X1)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_B)
% 6.33/6.57          | ~ (l1_pre_topc @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.33/6.57      inference('sup-', [status(thm)], ['3', '4'])).
% 6.33/6.57  thf('6', plain,
% 6.33/6.57      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('7', plain, ((v1_funct_1 @ sk_E_1)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('8', plain, ((v2_pre_topc @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('10', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1) @ 
% 6.33/6.57           (k1_zfmisc_1 @ 
% 6.33/6.57            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 6.33/6.57          | (v2_struct_0 @ X1)
% 6.33/6.57          | ~ (v2_pre_topc @ X1)
% 6.33/6.57          | ~ (l1_pre_topc @ X1)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.33/6.57      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 6.33/6.57  thf('11', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (l1_pre_topc @ sk_D)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (l1_pre_topc @ sk_D)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_D)
% 6.33/6.57          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1) @ 
% 6.33/6.57             (k1_zfmisc_1 @ 
% 6.33/6.57              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 6.33/6.57      inference('sup-', [status(thm)], ['2', '10'])).
% 6.33/6.57  thf('12', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(dt_m1_pre_topc, axiom,
% 6.33/6.57    (![A:$i]:
% 6.33/6.57     ( ( l1_pre_topc @ A ) =>
% 6.33/6.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 6.33/6.57  thf('13', plain,
% 6.33/6.57      (![X30 : $i, X31 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X30 @ X31)
% 6.33/6.57          | (l1_pre_topc @ X30)
% 6.33/6.57          | ~ (l1_pre_topc @ X31))),
% 6.33/6.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 6.33/6.57  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 6.33/6.57      inference('sup-', [status(thm)], ['12', '13'])).
% 6.33/6.57  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('16', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(cc1_pre_topc, axiom,
% 6.33/6.57    (![A:$i]:
% 6.33/6.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.33/6.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 6.33/6.57  thf('19', plain,
% 6.33/6.57      (![X27 : $i, X28 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X27 @ X28)
% 6.33/6.57          | (v2_pre_topc @ X27)
% 6.33/6.57          | ~ (l1_pre_topc @ X28)
% 6.33/6.57          | ~ (v2_pre_topc @ X28))),
% 6.33/6.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 6.33/6.57  thf('20', plain,
% 6.33/6.57      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 6.33/6.57      inference('sup-', [status(thm)], ['18', '19'])).
% 6.33/6.57  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('23', plain, ((v2_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 6.33/6.57  thf('24', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | (v2_struct_0 @ sk_D)
% 6.33/6.57          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1) @ 
% 6.33/6.57             (k1_zfmisc_1 @ 
% 6.33/6.57              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 6.33/6.57      inference('demod', [status(thm)], ['11', '16', '17', '23'])).
% 6.33/6.57  thf('25', plain,
% 6.33/6.57      (((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1) @ 
% 6.33/6.57         (k1_zfmisc_1 @ 
% 6.33/6.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 6.33/6.57        | (v2_struct_0 @ sk_D)
% 6.33/6.57        | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('sup-', [status(thm)], ['1', '24'])).
% 6.33/6.57  thf('26', plain, (~ (v2_struct_0 @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('27', plain,
% 6.33/6.57      (((v2_struct_0 @ sk_B)
% 6.33/6.57        | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1) @ 
% 6.33/6.57           (k1_zfmisc_1 @ 
% 6.33/6.57            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 6.33/6.57      inference('clc', [status(thm)], ['25', '26'])).
% 6.33/6.57  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('29', plain,
% 6.33/6.57      ((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1) @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('clc', [status(thm)], ['27', '28'])).
% 6.33/6.57  thf('30', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('31', plain,
% 6.33/6.57      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 6.33/6.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.33/6.57  thf('32', plain,
% 6.33/6.57      ((m1_subset_1 @ sk_E_1 @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(d5_tmap_1, axiom,
% 6.33/6.57    (![A:$i]:
% 6.33/6.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.33/6.57       ( ![B:$i]:
% 6.33/6.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.33/6.57             ( l1_pre_topc @ B ) ) =>
% 6.33/6.57           ( ![C:$i]:
% 6.33/6.57             ( ( m1_pre_topc @ C @ A ) =>
% 6.33/6.57               ( ![D:$i]:
% 6.33/6.57                 ( ( m1_pre_topc @ D @ A ) =>
% 6.33/6.57                   ( ![E:$i]:
% 6.33/6.57                     ( ( ( v1_funct_1 @ E ) & 
% 6.33/6.57                         ( v1_funct_2 @
% 6.33/6.57                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.33/6.57                         ( m1_subset_1 @
% 6.33/6.57                           E @ 
% 6.33/6.57                           ( k1_zfmisc_1 @
% 6.33/6.57                             ( k2_zfmisc_1 @
% 6.33/6.57                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.33/6.57                       ( ( m1_pre_topc @ D @ C ) =>
% 6.33/6.57                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 6.33/6.57                           ( k2_partfun1 @
% 6.33/6.57                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 6.33/6.57                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.33/6.57  thf('33', plain,
% 6.33/6.57      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 6.33/6.57         ((v2_struct_0 @ X33)
% 6.33/6.57          | ~ (v2_pre_topc @ X33)
% 6.33/6.57          | ~ (l1_pre_topc @ X33)
% 6.33/6.57          | ~ (m1_pre_topc @ X34 @ X35)
% 6.33/6.57          | ~ (m1_pre_topc @ X34 @ X36)
% 6.33/6.57          | ((k3_tmap_1 @ X35 @ X33 @ X36 @ X34 @ X37)
% 6.33/6.57              = (k2_partfun1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33) @ 
% 6.33/6.57                 X37 @ (u1_struct_0 @ X34)))
% 6.33/6.57          | ~ (m1_subset_1 @ X37 @ 
% 6.33/6.57               (k1_zfmisc_1 @ 
% 6.33/6.57                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33))))
% 6.33/6.57          | ~ (v1_funct_2 @ X37 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X33))
% 6.33/6.57          | ~ (v1_funct_1 @ X37)
% 6.33/6.57          | ~ (m1_pre_topc @ X36 @ X35)
% 6.33/6.57          | ~ (l1_pre_topc @ X35)
% 6.33/6.57          | ~ (v2_pre_topc @ X35)
% 6.33/6.57          | (v2_struct_0 @ X35))),
% 6.33/6.57      inference('cnf', [status(esa)], [d5_tmap_1])).
% 6.33/6.57  thf('34', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((v2_struct_0 @ X0)
% 6.33/6.57          | ~ (v2_pre_topc @ X0)
% 6.33/6.57          | ~ (l1_pre_topc @ X0)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 6.33/6.57          | ~ (v1_funct_1 @ sk_E_1)
% 6.33/6.57          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ 
% 6.33/6.57               (u1_struct_0 @ sk_B))
% 6.33/6.57          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E_1)
% 6.33/6.57              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57                 sk_E_1 @ (u1_struct_0 @ X1)))
% 6.33/6.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.33/6.57          | ~ (m1_pre_topc @ X1 @ X0)
% 6.33/6.57          | ~ (l1_pre_topc @ sk_B)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_B)
% 6.33/6.57          | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('sup-', [status(thm)], ['32', '33'])).
% 6.33/6.57  thf('35', plain, ((v1_funct_1 @ sk_E_1)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('36', plain,
% 6.33/6.57      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('37', plain,
% 6.33/6.57      ((m1_subset_1 @ sk_E_1 @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(redefinition_k2_partfun1, axiom,
% 6.33/6.57    (![A:$i,B:$i,C:$i,D:$i]:
% 6.33/6.57     ( ( ( v1_funct_1 @ C ) & 
% 6.33/6.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.33/6.57       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 6.33/6.57  thf('38', plain,
% 6.33/6.57      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 6.33/6.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 6.33/6.57          | ~ (v1_funct_1 @ X19)
% 6.33/6.57          | ((k2_partfun1 @ X20 @ X21 @ X19 @ X22) = (k7_relat_1 @ X19 @ X22)))),
% 6.33/6.57      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 6.33/6.57  thf('39', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57            sk_E_1 @ X0) = (k7_relat_1 @ sk_E_1 @ X0))
% 6.33/6.57          | ~ (v1_funct_1 @ sk_E_1))),
% 6.33/6.57      inference('sup-', [status(thm)], ['37', '38'])).
% 6.33/6.57  thf('40', plain, ((v1_funct_1 @ sk_E_1)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('41', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57           sk_E_1 @ X0) = (k7_relat_1 @ sk_E_1 @ X0))),
% 6.33/6.57      inference('demod', [status(thm)], ['39', '40'])).
% 6.33/6.57  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('44', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((v2_struct_0 @ X0)
% 6.33/6.57          | ~ (v2_pre_topc @ X0)
% 6.33/6.57          | ~ (l1_pre_topc @ X0)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 6.33/6.57          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E_1)
% 6.33/6.57              = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ X1)))
% 6.33/6.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.33/6.57          | ~ (m1_pre_topc @ X1 @ X0)
% 6.33/6.57          | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('demod', [status(thm)], ['34', '35', '36', '41', '42', '43'])).
% 6.33/6.57  thf('45', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (l1_pre_topc @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1)
% 6.33/6.57              = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ X0)))
% 6.33/6.57          | ~ (l1_pre_topc @ sk_D)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_D))),
% 6.33/6.57      inference('sup-', [status(thm)], ['31', '44'])).
% 6.33/6.57  thf('46', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('47', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('48', plain, ((v2_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 6.33/6.57  thf('49', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         ((v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1)
% 6.33/6.57              = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ X0)))
% 6.33/6.57          | (v2_struct_0 @ sk_D))),
% 6.33/6.57      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 6.33/6.57  thf('50', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         ((v2_struct_0 @ sk_D)
% 6.33/6.57          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1)
% 6.33/6.57              = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ X0)))
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('simplify', [status(thm)], ['49'])).
% 6.33/6.57  thf('51', plain,
% 6.33/6.57      (((v2_struct_0 @ sk_B)
% 6.33/6.57        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57            = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))
% 6.33/6.57        | (v2_struct_0 @ sk_D))),
% 6.33/6.57      inference('sup-', [status(thm)], ['30', '50'])).
% 6.33/6.57  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('53', plain,
% 6.33/6.57      (((v2_struct_0 @ sk_D)
% 6.33/6.57        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57            = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C))))),
% 6.33/6.57      inference('clc', [status(thm)], ['51', '52'])).
% 6.33/6.57  thf('54', plain, (~ (v2_struct_0 @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('55', plain,
% 6.33/6.57      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57         = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('clc', [status(thm)], ['53', '54'])).
% 6.33/6.57  thf('56', plain,
% 6.33/6.57      ((m1_subset_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('demod', [status(thm)], ['29', '55'])).
% 6.33/6.57  thf('57', plain,
% 6.33/6.57      ((m1_subset_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('demod', [status(thm)], ['29', '55'])).
% 6.33/6.57  thf('58', plain,
% 6.33/6.57      ((m1_subset_1 @ sk_F @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(d9_funct_2, axiom,
% 6.33/6.57    (![A:$i,B:$i,C:$i]:
% 6.33/6.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.33/6.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.33/6.57       ( ![D:$i]:
% 6.33/6.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.33/6.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.33/6.57           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 6.33/6.57             ( ![E:$i]:
% 6.33/6.57               ( ( m1_subset_1 @ E @ A ) =>
% 6.33/6.57                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 6.33/6.57  thf('59', plain,
% 6.33/6.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 6.33/6.57         (~ (v1_funct_1 @ X14)
% 6.33/6.57          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 6.33/6.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 6.33/6.57          | (m1_subset_1 @ (sk_E @ X14 @ X17 @ X15) @ X15)
% 6.33/6.57          | (r2_funct_2 @ X15 @ X16 @ X17 @ X14)
% 6.33/6.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 6.33/6.57          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 6.33/6.57          | ~ (v1_funct_1 @ X17))),
% 6.33/6.57      inference('cnf', [status(esa)], [d9_funct_2])).
% 6.33/6.57  thf('60', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (v1_funct_1 @ X0)
% 6.33/6.57          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.33/6.57          | ~ (m1_subset_1 @ X0 @ 
% 6.33/6.57               (k1_zfmisc_1 @ 
% 6.33/6.57                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 6.33/6.57          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0 @ 
% 6.33/6.57             sk_F)
% 6.33/6.57          | (m1_subset_1 @ (sk_E @ sk_F @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57             (u1_struct_0 @ sk_C))
% 6.33/6.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.33/6.57          | ~ (v1_funct_1 @ sk_F))),
% 6.33/6.57      inference('sup-', [status(thm)], ['58', '59'])).
% 6.33/6.57  thf('61', plain,
% 6.33/6.57      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('62', plain, ((v1_funct_1 @ sk_F)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('63', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (v1_funct_1 @ X0)
% 6.33/6.57          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.33/6.57          | ~ (m1_subset_1 @ X0 @ 
% 6.33/6.57               (k1_zfmisc_1 @ 
% 6.33/6.57                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 6.33/6.57          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ X0 @ 
% 6.33/6.57             sk_F)
% 6.33/6.57          | (m1_subset_1 @ (sk_E @ sk_F @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57             (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('demod', [status(thm)], ['60', '61', '62'])).
% 6.33/6.57  thf('64', plain,
% 6.33/6.57      (((m1_subset_1 @ 
% 6.33/6.57         (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57          (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57         (u1_struct_0 @ sk_C))
% 6.33/6.57        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57           (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 6.33/6.57        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.33/6.57        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C))))),
% 6.33/6.57      inference('sup-', [status(thm)], ['57', '63'])).
% 6.33/6.57  thf('65', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('66', plain,
% 6.33/6.57      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 6.33/6.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.33/6.57  thf('67', plain,
% 6.33/6.57      ((m1_subset_1 @ sk_E_1 @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('68', plain,
% 6.33/6.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X38 @ X39)
% 6.33/6.57          | ~ (m1_pre_topc @ X40 @ X39)
% 6.33/6.57          | ~ (l1_pre_topc @ X41)
% 6.33/6.57          | ~ (v2_pre_topc @ X41)
% 6.33/6.57          | (v2_struct_0 @ X41)
% 6.33/6.57          | ~ (l1_pre_topc @ X39)
% 6.33/6.57          | ~ (v2_pre_topc @ X39)
% 6.33/6.57          | (v2_struct_0 @ X39)
% 6.33/6.57          | ~ (v1_funct_1 @ X42)
% 6.33/6.57          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X41))
% 6.33/6.57          | ~ (m1_subset_1 @ X42 @ 
% 6.33/6.57               (k1_zfmisc_1 @ 
% 6.33/6.57                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X41))))
% 6.33/6.57          | (v1_funct_2 @ (k3_tmap_1 @ X39 @ X41 @ X40 @ X38 @ X42) @ 
% 6.33/6.57             (u1_struct_0 @ X38) @ (u1_struct_0 @ X41)))),
% 6.33/6.57      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.33/6.57  thf('69', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1) @ 
% 6.33/6.57           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 6.33/6.57          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ 
% 6.33/6.57               (u1_struct_0 @ sk_B))
% 6.33/6.57          | ~ (v1_funct_1 @ sk_E_1)
% 6.33/6.57          | (v2_struct_0 @ X1)
% 6.33/6.57          | ~ (v2_pre_topc @ X1)
% 6.33/6.57          | ~ (l1_pre_topc @ X1)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_B)
% 6.33/6.57          | ~ (l1_pre_topc @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.33/6.57      inference('sup-', [status(thm)], ['67', '68'])).
% 6.33/6.57  thf('70', plain,
% 6.33/6.57      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('71', plain, ((v1_funct_1 @ sk_E_1)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('72', plain, ((v2_pre_topc @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('74', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1) @ 
% 6.33/6.57           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 6.33/6.57          | (v2_struct_0 @ X1)
% 6.33/6.57          | ~ (v2_pre_topc @ X1)
% 6.33/6.57          | ~ (l1_pre_topc @ X1)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.33/6.57      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 6.33/6.57  thf('75', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (l1_pre_topc @ sk_D)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (l1_pre_topc @ sk_D)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_D)
% 6.33/6.57          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1) @ 
% 6.33/6.57             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 6.33/6.57      inference('sup-', [status(thm)], ['66', '74'])).
% 6.33/6.57  thf('76', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('77', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('78', plain, ((v2_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 6.33/6.57  thf('79', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | (v2_struct_0 @ sk_D)
% 6.33/6.57          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1) @ 
% 6.33/6.57             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 6.33/6.57      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 6.33/6.57  thf('80', plain,
% 6.33/6.57      (((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1) @ 
% 6.33/6.57         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.33/6.57        | (v2_struct_0 @ sk_D)
% 6.33/6.57        | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('sup-', [status(thm)], ['65', '79'])).
% 6.33/6.57  thf('81', plain, (~ (v2_struct_0 @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('82', plain,
% 6.33/6.57      (((v2_struct_0 @ sk_B)
% 6.33/6.57        | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1) @ 
% 6.33/6.57           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 6.33/6.57      inference('clc', [status(thm)], ['80', '81'])).
% 6.33/6.57  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('84', plain,
% 6.33/6.57      ((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1) @ 
% 6.33/6.57        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.33/6.57      inference('clc', [status(thm)], ['82', '83'])).
% 6.33/6.57  thf('85', plain,
% 6.33/6.57      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57         = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('clc', [status(thm)], ['53', '54'])).
% 6.33/6.57  thf('86', plain,
% 6.33/6.57      ((v1_funct_2 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.33/6.57      inference('demod', [status(thm)], ['84', '85'])).
% 6.33/6.57  thf('87', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('88', plain,
% 6.33/6.57      (![X45 : $i]: ((m1_pre_topc @ X45 @ X45) | ~ (l1_pre_topc @ X45))),
% 6.33/6.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 6.33/6.57  thf('89', plain,
% 6.33/6.57      ((m1_subset_1 @ sk_E_1 @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('90', plain,
% 6.33/6.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X38 @ X39)
% 6.33/6.57          | ~ (m1_pre_topc @ X40 @ X39)
% 6.33/6.57          | ~ (l1_pre_topc @ X41)
% 6.33/6.57          | ~ (v2_pre_topc @ X41)
% 6.33/6.57          | (v2_struct_0 @ X41)
% 6.33/6.57          | ~ (l1_pre_topc @ X39)
% 6.33/6.57          | ~ (v2_pre_topc @ X39)
% 6.33/6.57          | (v2_struct_0 @ X39)
% 6.33/6.57          | ~ (v1_funct_1 @ X42)
% 6.33/6.57          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X41))
% 6.33/6.57          | ~ (m1_subset_1 @ X42 @ 
% 6.33/6.57               (k1_zfmisc_1 @ 
% 6.33/6.57                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X41))))
% 6.33/6.57          | (v1_funct_1 @ (k3_tmap_1 @ X39 @ X41 @ X40 @ X38 @ X42)))),
% 6.33/6.57      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 6.33/6.57  thf('91', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1))
% 6.33/6.57          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ 
% 6.33/6.57               (u1_struct_0 @ sk_B))
% 6.33/6.57          | ~ (v1_funct_1 @ sk_E_1)
% 6.33/6.57          | (v2_struct_0 @ X1)
% 6.33/6.57          | ~ (v2_pre_topc @ X1)
% 6.33/6.57          | ~ (l1_pre_topc @ X1)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_B)
% 6.33/6.57          | ~ (l1_pre_topc @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.33/6.57      inference('sup-', [status(thm)], ['89', '90'])).
% 6.33/6.57  thf('92', plain,
% 6.33/6.57      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('93', plain, ((v1_funct_1 @ sk_E_1)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('96', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E_1))
% 6.33/6.57          | (v2_struct_0 @ X1)
% 6.33/6.57          | ~ (v2_pre_topc @ X1)
% 6.33/6.57          | ~ (l1_pre_topc @ X1)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 6.33/6.57      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 6.33/6.57  thf('97', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (l1_pre_topc @ sk_D)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (l1_pre_topc @ sk_D)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_D)
% 6.33/6.57          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1)))),
% 6.33/6.57      inference('sup-', [status(thm)], ['88', '96'])).
% 6.33/6.57  thf('98', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('99', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('100', plain, ((v2_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['20', '21', '22'])).
% 6.33/6.57  thf('101', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | (v2_struct_0 @ sk_B)
% 6.33/6.57          | (v2_struct_0 @ sk_D)
% 6.33/6.57          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E_1)))),
% 6.33/6.57      inference('demod', [status(thm)], ['97', '98', '99', '100'])).
% 6.33/6.57  thf('102', plain,
% 6.33/6.57      (((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1))
% 6.33/6.57        | (v2_struct_0 @ sk_D)
% 6.33/6.57        | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('sup-', [status(thm)], ['87', '101'])).
% 6.33/6.57  thf('103', plain, (~ (v2_struct_0 @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('104', plain,
% 6.33/6.57      (((v2_struct_0 @ sk_B)
% 6.33/6.57        | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1)))),
% 6.33/6.57      inference('clc', [status(thm)], ['102', '103'])).
% 6.33/6.57  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('106', plain,
% 6.33/6.57      ((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1))),
% 6.33/6.57      inference('clc', [status(thm)], ['104', '105'])).
% 6.33/6.57  thf('107', plain,
% 6.33/6.57      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57         = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('clc', [status(thm)], ['53', '54'])).
% 6.33/6.57  thf('108', plain,
% 6.33/6.57      ((v1_funct_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('demod', [status(thm)], ['106', '107'])).
% 6.33/6.57  thf('109', plain,
% 6.33/6.57      (((m1_subset_1 @ 
% 6.33/6.57         (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57          (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57         (u1_struct_0 @ sk_C))
% 6.33/6.57        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57           (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 6.33/6.57      inference('demod', [status(thm)], ['64', '86', '108'])).
% 6.33/6.57  thf(t2_subset, axiom,
% 6.33/6.57    (![A:$i,B:$i]:
% 6.33/6.57     ( ( m1_subset_1 @ A @ B ) =>
% 6.33/6.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 6.33/6.57  thf('110', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((r2_hidden @ X0 @ X1)
% 6.33/6.57          | (v1_xboole_0 @ X1)
% 6.33/6.57          | ~ (m1_subset_1 @ X0 @ X1))),
% 6.33/6.57      inference('cnf', [status(esa)], [t2_subset])).
% 6.33/6.57  thf('111', plain,
% 6.33/6.57      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57         (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 6.33/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.33/6.57        | (r2_hidden @ 
% 6.33/6.57           (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57            (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57           (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('sup-', [status(thm)], ['109', '110'])).
% 6.33/6.57  thf('112', plain,
% 6.33/6.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1) @ sk_F)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('113', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('114', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('115', plain,
% 6.33/6.57      (![X0 : $i, X1 : $i]:
% 6.33/6.57         ((v2_struct_0 @ X0)
% 6.33/6.57          | ~ (v2_pre_topc @ X0)
% 6.33/6.57          | ~ (l1_pre_topc @ X0)
% 6.33/6.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 6.33/6.57          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E_1)
% 6.33/6.57              = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ X1)))
% 6.33/6.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 6.33/6.57          | ~ (m1_pre_topc @ X1 @ X0)
% 6.33/6.57          | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('demod', [status(thm)], ['34', '35', '36', '41', '42', '43'])).
% 6.33/6.57  thf('116', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         ((v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E_1)
% 6.33/6.57              = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ X0)))
% 6.33/6.57          | ~ (l1_pre_topc @ sk_A)
% 6.33/6.57          | ~ (v2_pre_topc @ sk_A)
% 6.33/6.57          | (v2_struct_0 @ sk_A))),
% 6.33/6.57      inference('sup-', [status(thm)], ['114', '115'])).
% 6.33/6.57  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('119', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         ((v2_struct_0 @ sk_B)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.33/6.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 6.33/6.57          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E_1)
% 6.33/6.57              = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ X0)))
% 6.33/6.57          | (v2_struct_0 @ sk_A))),
% 6.33/6.57      inference('demod', [status(thm)], ['116', '117', '118'])).
% 6.33/6.57  thf('120', plain,
% 6.33/6.57      (((v2_struct_0 @ sk_A)
% 6.33/6.57        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57            = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))
% 6.33/6.57        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 6.33/6.57        | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('sup-', [status(thm)], ['113', '119'])).
% 6.33/6.57  thf('121', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('122', plain,
% 6.33/6.57      (((v2_struct_0 @ sk_A)
% 6.33/6.57        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57            = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))
% 6.33/6.57        | (v2_struct_0 @ sk_B))),
% 6.33/6.57      inference('demod', [status(thm)], ['120', '121'])).
% 6.33/6.57  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('124', plain,
% 6.33/6.57      (((v2_struct_0 @ sk_B)
% 6.33/6.57        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57            = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C))))),
% 6.33/6.57      inference('clc', [status(thm)], ['122', '123'])).
% 6.33/6.57  thf('125', plain, (~ (v2_struct_0 @ sk_B)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('126', plain,
% 6.33/6.57      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E_1)
% 6.33/6.57         = (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('clc', [status(thm)], ['124', '125'])).
% 6.33/6.57  thf('127', plain,
% 6.33/6.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57          (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)),
% 6.33/6.57      inference('demod', [status(thm)], ['112', '126'])).
% 6.33/6.57  thf('128', plain,
% 6.33/6.57      (((r2_hidden @ 
% 6.33/6.57         (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57          (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57         (u1_struct_0 @ sk_C))
% 6.33/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('clc', [status(thm)], ['111', '127'])).
% 6.33/6.57  thf('129', plain,
% 6.33/6.57      (![X46 : $i]:
% 6.33/6.57         (~ (r2_hidden @ X46 @ (u1_struct_0 @ sk_C))
% 6.33/6.57          | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57              sk_E_1 @ X46) = (k1_funct_1 @ sk_F @ X46))
% 6.33/6.57          | ~ (m1_subset_1 @ X46 @ (u1_struct_0 @ sk_D)))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('130', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(t1_tsep_1, axiom,
% 6.33/6.57    (![A:$i]:
% 6.33/6.57     ( ( l1_pre_topc @ A ) =>
% 6.33/6.57       ( ![B:$i]:
% 6.33/6.57         ( ( m1_pre_topc @ B @ A ) =>
% 6.33/6.57           ( m1_subset_1 @
% 6.33/6.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 6.33/6.57  thf('131', plain,
% 6.33/6.57      (![X43 : $i, X44 : $i]:
% 6.33/6.57         (~ (m1_pre_topc @ X43 @ X44)
% 6.33/6.57          | (m1_subset_1 @ (u1_struct_0 @ X43) @ 
% 6.33/6.57             (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 6.33/6.57          | ~ (l1_pre_topc @ X44))),
% 6.33/6.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 6.33/6.57  thf('132', plain,
% 6.33/6.57      ((~ (l1_pre_topc @ sk_D)
% 6.33/6.57        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 6.33/6.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 6.33/6.57      inference('sup-', [status(thm)], ['130', '131'])).
% 6.33/6.57  thf('133', plain, ((l1_pre_topc @ sk_D)),
% 6.33/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.33/6.57  thf('134', plain,
% 6.33/6.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 6.33/6.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 6.33/6.57      inference('demod', [status(thm)], ['132', '133'])).
% 6.33/6.57  thf(t4_subset, axiom,
% 6.33/6.57    (![A:$i,B:$i,C:$i]:
% 6.33/6.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 6.33/6.57       ( m1_subset_1 @ A @ C ) ))).
% 6.33/6.57  thf('135', plain,
% 6.33/6.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.33/6.57         (~ (r2_hidden @ X2 @ X3)
% 6.33/6.57          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 6.33/6.57          | (m1_subset_1 @ X2 @ X4))),
% 6.33/6.57      inference('cnf', [status(esa)], [t4_subset])).
% 6.33/6.57  thf('136', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.33/6.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('sup-', [status(thm)], ['134', '135'])).
% 6.33/6.57  thf('137', plain,
% 6.33/6.57      (![X46 : $i]:
% 6.33/6.57         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57            sk_E_1 @ X46) = (k1_funct_1 @ sk_F @ X46))
% 6.33/6.57          | ~ (r2_hidden @ X46 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('clc', [status(thm)], ['129', '136'])).
% 6.33/6.57  thf('138', plain,
% 6.33/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.33/6.57        | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57            sk_E_1 @ 
% 6.33/6.57            (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57             (u1_struct_0 @ sk_C)))
% 6.33/6.57            = (k1_funct_1 @ sk_F @ 
% 6.33/6.57               (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57                (u1_struct_0 @ sk_C)))))),
% 6.33/6.57      inference('sup-', [status(thm)], ['128', '137'])).
% 6.33/6.57  thf('139', plain,
% 6.33/6.57      (((r2_hidden @ 
% 6.33/6.57         (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57          (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57         (u1_struct_0 @ sk_C))
% 6.33/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('clc', [status(thm)], ['111', '127'])).
% 6.33/6.57  thf('140', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.33/6.57          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('sup-', [status(thm)], ['134', '135'])).
% 6.33/6.57  thf('141', plain,
% 6.33/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.33/6.57        | (m1_subset_1 @ 
% 6.33/6.57           (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57            (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57           (u1_struct_0 @ sk_D)))),
% 6.33/6.57      inference('sup-', [status(thm)], ['139', '140'])).
% 6.33/6.57  thf('142', plain,
% 6.33/6.57      ((m1_subset_1 @ sk_E_1 @ 
% 6.33/6.57        (k1_zfmisc_1 @ 
% 6.33/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf(redefinition_k3_funct_2, axiom,
% 6.33/6.57    (![A:$i,B:$i,C:$i,D:$i]:
% 6.33/6.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 6.33/6.57         ( v1_funct_2 @ C @ A @ B ) & 
% 6.33/6.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.33/6.57         ( m1_subset_1 @ D @ A ) ) =>
% 6.33/6.57       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 6.33/6.57  thf('143', plain,
% 6.33/6.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 6.33/6.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 6.33/6.57          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 6.33/6.57          | ~ (v1_funct_1 @ X23)
% 6.33/6.57          | (v1_xboole_0 @ X24)
% 6.33/6.57          | ~ (m1_subset_1 @ X26 @ X24)
% 6.33/6.57          | ((k3_funct_2 @ X24 @ X25 @ X23 @ X26) = (k1_funct_1 @ X23 @ X26)))),
% 6.33/6.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 6.33/6.57  thf('144', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57            sk_E_1 @ X0) = (k1_funct_1 @ sk_E_1 @ X0))
% 6.33/6.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.33/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.33/6.57          | ~ (v1_funct_1 @ sk_E_1)
% 6.33/6.57          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ 
% 6.33/6.57               (u1_struct_0 @ sk_B)))),
% 6.33/6.57      inference('sup-', [status(thm)], ['142', '143'])).
% 6.33/6.57  thf('145', plain, ((v1_funct_1 @ sk_E_1)),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('146', plain,
% 6.33/6.57      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 6.33/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.33/6.57  thf('147', plain,
% 6.33/6.57      (![X0 : $i]:
% 6.33/6.57         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57            sk_E_1 @ X0) = (k1_funct_1 @ sk_E_1 @ X0))
% 6.33/6.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.33/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 6.33/6.57      inference('demod', [status(thm)], ['144', '145', '146'])).
% 6.33/6.57  thf('148', plain,
% 6.33/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.33/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.33/6.57        | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 6.33/6.57            sk_E_1 @ 
% 6.33/6.57            (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57             (u1_struct_0 @ sk_C)))
% 6.33/6.57            = (k1_funct_1 @ sk_E_1 @ 
% 6.33/6.57               (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57                (u1_struct_0 @ sk_C)))))),
% 6.33/6.57      inference('sup-', [status(thm)], ['141', '147'])).
% 6.33/6.57  thf('149', plain,
% 6.33/6.57      ((((k1_funct_1 @ sk_F @ 
% 6.33/6.57          (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57           (u1_struct_0 @ sk_C)))
% 6.33/6.57          = (k1_funct_1 @ sk_E_1 @ 
% 6.33/6.57             (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.33/6.57              (u1_struct_0 @ sk_C))))
% 6.33/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.33/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.33/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 6.33/6.57      inference('sup+', [status(thm)], ['138', '148'])).
% 6.33/6.57  thf('150', plain,
% 6.33/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.33/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.40/6.57        | ((k1_funct_1 @ sk_F @ 
% 6.40/6.57            (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57             (u1_struct_0 @ sk_C)))
% 6.40/6.57            = (k1_funct_1 @ sk_E_1 @ 
% 6.40/6.57               (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57                (u1_struct_0 @ sk_C)))))),
% 6.40/6.57      inference('simplify', [status(thm)], ['149'])).
% 6.40/6.57  thf('151', plain,
% 6.40/6.57      (((r2_hidden @ 
% 6.40/6.57         (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57          (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57         (u1_struct_0 @ sk_C))
% 6.40/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 6.40/6.57      inference('clc', [status(thm)], ['111', '127'])).
% 6.40/6.57  thf(t72_funct_1, axiom,
% 6.40/6.57    (![A:$i,B:$i,C:$i]:
% 6.40/6.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 6.40/6.57       ( ( r2_hidden @ A @ B ) =>
% 6.40/6.57         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 6.40/6.57  thf('152', plain,
% 6.40/6.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.40/6.57         (~ (r2_hidden @ X8 @ X9)
% 6.40/6.57          | ~ (v1_relat_1 @ X10)
% 6.40/6.57          | ~ (v1_funct_1 @ X10)
% 6.40/6.57          | ((k1_funct_1 @ (k7_relat_1 @ X10 @ X9) @ X8)
% 6.40/6.57              = (k1_funct_1 @ X10 @ X8)))),
% 6.40/6.57      inference('cnf', [status(esa)], [t72_funct_1])).
% 6.40/6.57  thf('153', plain,
% 6.40/6.57      (![X0 : $i]:
% 6.40/6.57         ((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.40/6.57          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57              (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57               (u1_struct_0 @ sk_C)))
% 6.40/6.57              = (k1_funct_1 @ X0 @ 
% 6.40/6.57                 (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57                  (u1_struct_0 @ sk_C))))
% 6.40/6.57          | ~ (v1_funct_1 @ X0)
% 6.40/6.57          | ~ (v1_relat_1 @ X0))),
% 6.40/6.57      inference('sup-', [status(thm)], ['151', '152'])).
% 6.40/6.57  thf('154', plain,
% 6.40/6.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 6.40/6.57         (~ (v1_funct_1 @ X14)
% 6.40/6.57          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 6.40/6.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 6.40/6.57          | ((k1_funct_1 @ X17 @ (sk_E @ X14 @ X17 @ X15))
% 6.40/6.57              != (k1_funct_1 @ X14 @ (sk_E @ X14 @ X17 @ X15)))
% 6.40/6.57          | (r2_funct_2 @ X15 @ X16 @ X17 @ X14)
% 6.40/6.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 6.40/6.57          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 6.40/6.57          | ~ (v1_funct_1 @ X17))),
% 6.40/6.57      inference('cnf', [status(esa)], [d9_funct_2])).
% 6.40/6.57  thf('155', plain,
% 6.40/6.57      (![X0 : $i]:
% 6.40/6.57         (((k1_funct_1 @ sk_E_1 @ 
% 6.40/6.57            (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57             (u1_struct_0 @ sk_C)))
% 6.40/6.57            != (k1_funct_1 @ sk_F @ 
% 6.40/6.57                (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57                 (u1_struct_0 @ sk_C))))
% 6.40/6.57          | ~ (v1_relat_1 @ sk_E_1)
% 6.40/6.57          | ~ (v1_funct_1 @ sk_E_1)
% 6.40/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.40/6.57          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))
% 6.40/6.57          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57               (u1_struct_0 @ sk_C) @ X0)
% 6.40/6.57          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 6.40/6.57          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 6.40/6.57             (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 6.40/6.57          | ~ (m1_subset_1 @ sk_F @ 
% 6.40/6.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 6.40/6.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ X0)
% 6.40/6.57          | ~ (v1_funct_1 @ sk_F))),
% 6.40/6.57      inference('sup-', [status(thm)], ['153', '154'])).
% 6.40/6.57  thf('156', plain,
% 6.40/6.57      ((m1_subset_1 @ sk_E_1 @ 
% 6.40/6.57        (k1_zfmisc_1 @ 
% 6.40/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 6.40/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.40/6.57  thf(cc1_relset_1, axiom,
% 6.40/6.57    (![A:$i,B:$i,C:$i]:
% 6.40/6.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.40/6.57       ( v1_relat_1 @ C ) ))).
% 6.40/6.57  thf('157', plain,
% 6.40/6.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.40/6.57         ((v1_relat_1 @ X11)
% 6.40/6.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 6.40/6.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.40/6.57  thf('158', plain, ((v1_relat_1 @ sk_E_1)),
% 6.40/6.57      inference('sup-', [status(thm)], ['156', '157'])).
% 6.40/6.57  thf('159', plain, ((v1_funct_1 @ sk_E_1)),
% 6.40/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.40/6.57  thf('160', plain,
% 6.40/6.57      ((v1_funct_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)))),
% 6.40/6.57      inference('demod', [status(thm)], ['106', '107'])).
% 6.40/6.57  thf('161', plain, ((v1_funct_1 @ sk_F)),
% 6.40/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.40/6.57  thf('162', plain,
% 6.40/6.57      (![X0 : $i]:
% 6.40/6.57         (((k1_funct_1 @ sk_E_1 @ 
% 6.40/6.57            (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57             (u1_struct_0 @ sk_C)))
% 6.40/6.57            != (k1_funct_1 @ sk_F @ 
% 6.40/6.57                (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57                 (u1_struct_0 @ sk_C))))
% 6.40/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.40/6.57          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57               (u1_struct_0 @ sk_C) @ X0)
% 6.40/6.57          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 6.40/6.57          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 6.40/6.57             (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 6.40/6.57          | ~ (m1_subset_1 @ sk_F @ 
% 6.40/6.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 6.40/6.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ X0))),
% 6.40/6.57      inference('demod', [status(thm)], ['155', '158', '159', '160', '161'])).
% 6.40/6.57  thf('163', plain,
% 6.40/6.57      (![X0 : $i]:
% 6.40/6.57         (((k1_funct_1 @ sk_E_1 @ 
% 6.40/6.57            (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57             (u1_struct_0 @ sk_C)))
% 6.40/6.57            != (k1_funct_1 @ sk_E_1 @ 
% 6.40/6.57                (sk_E @ sk_F @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57                 (u1_struct_0 @ sk_C))))
% 6.40/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.40/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.40/6.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ X0)
% 6.40/6.57          | ~ (m1_subset_1 @ sk_F @ 
% 6.40/6.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 6.40/6.57          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 6.40/6.57             (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 6.40/6.57          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 6.40/6.57          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57               (u1_struct_0 @ sk_C) @ X0)
% 6.40/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 6.40/6.57      inference('sup-', [status(thm)], ['150', '162'])).
% 6.40/6.57  thf('164', plain,
% 6.40/6.57      (![X0 : $i]:
% 6.40/6.57         (~ (v1_funct_2 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57             (u1_struct_0 @ sk_C) @ X0)
% 6.40/6.57          | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 6.40/6.57          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ X0 @ 
% 6.40/6.57             (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 6.40/6.57          | ~ (m1_subset_1 @ sk_F @ 
% 6.40/6.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 6.40/6.57          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ X0)
% 6.40/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.40/6.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 6.40/6.57      inference('simplify', [status(thm)], ['163'])).
% 6.40/6.57  thf('165', plain,
% 6.40/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.40/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.40/6.57        | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 6.40/6.57        | ~ (m1_subset_1 @ sk_F @ 
% 6.40/6.57             (k1_zfmisc_1 @ 
% 6.40/6.57              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 6.40/6.57        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.40/6.57           (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 6.40/6.57        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 6.40/6.57      inference('sup-', [status(thm)], ['56', '164'])).
% 6.40/6.57  thf('166', plain,
% 6.40/6.57      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.40/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.40/6.57  thf('167', plain,
% 6.40/6.57      ((m1_subset_1 @ sk_F @ 
% 6.40/6.57        (k1_zfmisc_1 @ 
% 6.40/6.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 6.40/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.40/6.57  thf('168', plain,
% 6.40/6.57      ((v1_funct_2 @ (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ 
% 6.40/6.57        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 6.40/6.57      inference('demod', [status(thm)], ['84', '85'])).
% 6.40/6.57  thf('169', plain,
% 6.40/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.40/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.40/6.57        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.40/6.57           (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 6.40/6.57      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 6.40/6.57  thf('170', plain,
% 6.40/6.57      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.40/6.57          (k7_relat_1 @ sk_E_1 @ (u1_struct_0 @ sk_C)) @ sk_F)),
% 6.40/6.57      inference('demod', [status(thm)], ['112', '126'])).
% 6.40/6.57  thf('171', plain,
% 6.40/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 6.40/6.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 6.40/6.57      inference('clc', [status(thm)], ['169', '170'])).
% 6.40/6.57  thf(fc2_struct_0, axiom,
% 6.40/6.57    (![A:$i]:
% 6.40/6.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 6.40/6.57       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.40/6.57  thf('172', plain,
% 6.40/6.57      (![X32 : $i]:
% 6.40/6.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 6.40/6.57          | ~ (l1_struct_0 @ X32)
% 6.40/6.57          | (v2_struct_0 @ X32))),
% 6.40/6.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 6.40/6.57  thf('173', plain,
% 6.40/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 6.40/6.57        | (v2_struct_0 @ sk_D)
% 6.40/6.57        | ~ (l1_struct_0 @ sk_D))),
% 6.40/6.57      inference('sup-', [status(thm)], ['171', '172'])).
% 6.40/6.57  thf('174', plain, ((l1_pre_topc @ sk_D)),
% 6.40/6.57      inference('demod', [status(thm)], ['14', '15'])).
% 6.40/6.57  thf(dt_l1_pre_topc, axiom,
% 6.40/6.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 6.40/6.57  thf('175', plain,
% 6.40/6.57      (![X29 : $i]: ((l1_struct_0 @ X29) | ~ (l1_pre_topc @ X29))),
% 6.40/6.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 6.40/6.57  thf('176', plain, ((l1_struct_0 @ sk_D)),
% 6.40/6.57      inference('sup-', [status(thm)], ['174', '175'])).
% 6.40/6.57  thf('177', plain,
% 6.40/6.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C)) | (v2_struct_0 @ sk_D))),
% 6.40/6.57      inference('demod', [status(thm)], ['173', '176'])).
% 6.40/6.57  thf('178', plain, (~ (v2_struct_0 @ sk_D)),
% 6.40/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.40/6.57  thf('179', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 6.40/6.57      inference('clc', [status(thm)], ['177', '178'])).
% 6.40/6.57  thf('180', plain,
% 6.40/6.57      (![X32 : $i]:
% 6.40/6.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 6.40/6.57          | ~ (l1_struct_0 @ X32)
% 6.40/6.57          | (v2_struct_0 @ X32))),
% 6.40/6.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 6.40/6.57  thf('181', plain, (((v2_struct_0 @ sk_C) | ~ (l1_struct_0 @ sk_C))),
% 6.40/6.57      inference('sup-', [status(thm)], ['179', '180'])).
% 6.40/6.57  thf('182', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 6.40/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.40/6.57  thf('183', plain,
% 6.40/6.57      (![X30 : $i, X31 : $i]:
% 6.40/6.57         (~ (m1_pre_topc @ X30 @ X31)
% 6.40/6.57          | (l1_pre_topc @ X30)
% 6.40/6.57          | ~ (l1_pre_topc @ X31))),
% 6.40/6.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 6.40/6.57  thf('184', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 6.40/6.57      inference('sup-', [status(thm)], ['182', '183'])).
% 6.40/6.57  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 6.40/6.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.40/6.57  thf('186', plain, ((l1_pre_topc @ sk_C)),
% 6.40/6.57      inference('demod', [status(thm)], ['184', '185'])).
% 6.40/6.57  thf('187', plain,
% 6.40/6.57      (![X29 : $i]: ((l1_struct_0 @ X29) | ~ (l1_pre_topc @ X29))),
% 6.40/6.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 6.40/6.57  thf('188', plain, ((l1_struct_0 @ sk_C)),
% 6.40/6.57      inference('sup-', [status(thm)], ['186', '187'])).
% 6.40/6.57  thf('189', plain, ((v2_struct_0 @ sk_C)),
% 6.40/6.57      inference('demod', [status(thm)], ['181', '188'])).
% 6.40/6.57  thf('190', plain, ($false), inference('demod', [status(thm)], ['0', '189'])).
% 6.40/6.57  
% 6.40/6.57  % SZS output end Refutation
% 6.40/6.57  
% 6.40/6.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
