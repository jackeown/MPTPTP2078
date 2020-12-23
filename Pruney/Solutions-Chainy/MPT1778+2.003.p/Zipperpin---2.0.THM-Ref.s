%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxjmX0AAG3

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 843 expanded)
%              Number of leaves         :   41 ( 263 expanded)
%              Depth                    :   23
%              Number of atoms          : 2018 (36246 expanded)
%              Number of equality atoms :   33 ( 103 expanded)
%              Maximal formula depth    :   24 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(t89_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( v5_pre_topc @ E @ C @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ D @ C )
                       => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
                          & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B )
                          & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                          & ( v5_pre_topc @ E @ C @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ D @ C )
                         => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
                            & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B )
                            & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t89_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ~ ( v2_struct_0 @ D )
        & ( m1_pre_topc @ D @ A ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v5_pre_topc @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X26 @ X27 @ X25 @ X28 ) @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_tmap_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('7',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 ) @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','10','15','16','17','18','19','20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X23 )
      | ( ( k3_tmap_1 @ X22 @ X20 @ X23 @ X21 @ X24 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X20 ) @ X24 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_C )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( m1_pre_topc @ sk_D @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( ( k2_tmap_1 @ X18 @ X16 @ X19 @ X17 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X19 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('45',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_D @ sk_B )
   <= ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['24','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('64',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( r1_tarski @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['13','14'])).

thf('67',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
        & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) )).

thf('69',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( zip_tseitin_1 @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( zip_tseitin_0 @ X9 @ X6 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_E @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_E @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( zip_tseitin_0 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_funct_2 @ ( k2_partfun1 @ X0 @ X1 @ X2 @ X3 ) @ X3 @ X1 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('76',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('78',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['23'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('85',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('86',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('89',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( zip_tseitin_0 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ X0 @ X1 @ X2 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('96',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('98',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['23'])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('104',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('106',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['88','89'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( zip_tseitin_0 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('114',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('116',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('118',plain,
    ( ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['23'])).

thf('119',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( zip_tseitin_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('122',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('124',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('126',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['88','89'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['23'])).

thf('131',plain,(
    ~ ( v5_pre_topc @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['93','111','129','130'])).

thf('132',plain,(
    ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D ) @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','131'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    $false ),
    inference(demod,[status(thm)],['0','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wxjmX0AAG3
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:12:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 112 iterations in 0.053s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.21/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.51  thf(t89_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                         ( v1_funct_2 @
% 0.21/0.51                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                         ( v5_pre_topc @ E @ C @ B ) & 
% 0.21/0.51                         ( m1_subset_1 @
% 0.21/0.51                           E @ 
% 0.21/0.51                           ( k1_zfmisc_1 @
% 0.21/0.51                             ( k2_zfmisc_1 @
% 0.21/0.51                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.51                         ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.21/0.51                           ( v1_funct_2 @
% 0.21/0.51                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.51                             ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                           ( v5_pre_topc @
% 0.21/0.51                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B ) & 
% 0.21/0.51                           ( m1_subset_1 @
% 0.21/0.51                             ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.51                             ( k1_zfmisc_1 @
% 0.21/0.51                               ( k2_zfmisc_1 @
% 0.21/0.51                                 ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51                ( l1_pre_topc @ B ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                      ( ![E:$i]:
% 0.21/0.51                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                            ( v1_funct_2 @
% 0.21/0.51                              E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                            ( v5_pre_topc @ E @ C @ B ) & 
% 0.21/0.51                            ( m1_subset_1 @
% 0.21/0.51                              E @ 
% 0.21/0.51                              ( k1_zfmisc_1 @
% 0.21/0.51                                ( k2_zfmisc_1 @
% 0.21/0.51                                  ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51                          ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.51                            ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.21/0.51                              ( v1_funct_2 @
% 0.21/0.51                                ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.51                                ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                              ( v5_pre_topc @
% 0.21/0.51                                ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ D @ B ) & 
% 0.21/0.51                              ( m1_subset_1 @
% 0.21/0.51                                ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.51                                ( k1_zfmisc_1 @
% 0.21/0.51                                  ( k2_zfmisc_1 @
% 0.21/0.51                                    ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t89_tmap_1])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(fc2_tmap_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.21/0.51         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( v1_funct_1 @ C ) & 
% 0.21/0.51         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51         ( v5_pre_topc @ C @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           C @ 
% 0.21/0.51           ( k1_zfmisc_1 @
% 0.21/0.51             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.21/0.51         ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.51         ( v1_funct_2 @
% 0.21/0.51           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.21/0.51           ( u1_struct_0 @ B ) ) & 
% 0.21/0.51         ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X25 @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X27))))
% 0.21/0.51          | ~ (v5_pre_topc @ X25 @ X26 @ X27)
% 0.21/0.51          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X27))
% 0.21/0.51          | ~ (v1_funct_1 @ X25)
% 0.21/0.51          | ~ (l1_pre_topc @ X27)
% 0.21/0.51          | ~ (v2_pre_topc @ X27)
% 0.21/0.51          | (v2_struct_0 @ X27)
% 0.21/0.51          | ~ (l1_pre_topc @ X26)
% 0.21/0.51          | ~ (v2_pre_topc @ X26)
% 0.21/0.51          | (v2_struct_0 @ X26)
% 0.21/0.51          | (v2_struct_0 @ X28)
% 0.21/0.51          | ~ (m1_pre_topc @ X28 @ X26)
% 0.21/0.51          | (v5_pre_topc @ (k2_tmap_1 @ X26 @ X27 @ X25 @ X28) @ X28 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_tmap_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ X0 @ sk_B)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ sk_C)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_C)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_C)
% 0.21/0.51          | (v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (v5_pre_topc @ sk_E @ sk_C @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.51          | (v2_pre_topc @ X10)
% 0.21/0.51          | ~ (l1_pre_topc @ X11)
% 0.21/0.51          | ~ (v2_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, ((v2_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.51  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.51          | (l1_pre_topc @ X13)
% 0.21/0.51          | ~ (l1_pre_topc @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain, ((v5_pre_topc @ sk_E @ sk_C @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0) @ X0 @ sk_B)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.21/0.51          | (v2_struct_0 @ X0)
% 0.21/0.51          | (v2_struct_0 @ sk_C)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['4', '10', '15', '16', '17', '18', '19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | (v2_struct_0 @ sk_C)
% 0.21/0.51        | (v2_struct_0 @ sk_D)
% 0.21/0.51        | (v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ sk_D @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))
% 0.21/0.51        | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.21/0.51        | ~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51             sk_D @ sk_B)
% 0.21/0.51        | ~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51             (k1_zfmisc_1 @ 
% 0.21/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((~ (v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51           sk_D @ sk_B))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               sk_D @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d5_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.51                         ( v1_funct_2 @
% 0.21/0.51                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                         ( m1_subset_1 @
% 0.21/0.51                           E @ 
% 0.21/0.51                           ( k1_zfmisc_1 @
% 0.21/0.51                             ( k2_zfmisc_1 @
% 0.21/0.51                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.51                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.51                           ( k2_partfun1 @
% 0.21/0.51                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.21/0.51                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X20)
% 0.21/0.51          | ~ (v2_pre_topc @ X20)
% 0.21/0.51          | ~ (l1_pre_topc @ X20)
% 0.21/0.51          | ~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.51          | ~ (m1_pre_topc @ X21 @ X23)
% 0.21/0.51          | ((k3_tmap_1 @ X22 @ X20 @ X23 @ X21 @ X24)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20) @ 
% 0.21/0.51                 X24 @ (u1_struct_0 @ X21)))
% 0.21/0.51          | ~ (m1_subset_1 @ X24 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20))))
% 0.21/0.51          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (v1_funct_1 @ X24)
% 0.21/0.51          | ~ (m1_pre_topc @ X23 @ X22)
% 0.21/0.51          | ~ (l1_pre_topc @ X22)
% 0.21/0.51          | ~ (v2_pre_topc @ X22)
% 0.21/0.51          | (v2_struct_0 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.51          | ((k3_tmap_1 @ X0 @ sk_B @ sk_C @ X1 @ sk_E)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ sk_C)
% 0.21/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.21/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '34'])).
% 0.21/0.51  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_B)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.21/0.51          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 @ sk_E)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.51          | (v2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51               sk_E @ (u1_struct_0 @ sk_D)))
% 0.21/0.51        | ~ (m1_pre_topc @ sk_D @ sk_C)
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '38'])).
% 0.21/0.51  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d4_tmap_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.51             ( l1_pre_topc @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.51                 ( m1_subset_1 @
% 0.21/0.51                   C @ 
% 0.21/0.51                   ( k1_zfmisc_1 @
% 0.21/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.51                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.21/0.51                     ( k2_partfun1 @
% 0.21/0.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.51                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         ((v2_struct_0 @ X16)
% 0.21/0.51          | ~ (v2_pre_topc @ X16)
% 0.21/0.51          | ~ (l1_pre_topc @ X16)
% 0.21/0.51          | ~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.51          | ((k2_tmap_1 @ X18 @ X16 @ X19 @ X17)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ 
% 0.21/0.51                 X19 @ (u1_struct_0 @ X17)))
% 0.21/0.51          | ~ (m1_subset_1 @ X19 @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 0.21/0.51          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 0.21/0.51          | ~ (v1_funct_1 @ X19)
% 0.21/0.51          | ~ (l1_pre_topc @ X18)
% 0.21/0.51          | ~ (v2_pre_topc @ X18)
% 0.21/0.51          | (v2_struct_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_C)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_C)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_C)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain, ((v2_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.51  thf('45', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('49', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v2_struct_0 @ sk_C)
% 0.21/0.51          | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ X0)
% 0.21/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.21/0.51          | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)],
% 0.21/0.51                ['43', '44', '45', '46', '47', '48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.21/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51               sk_E @ (u1_struct_0 @ sk_D)))
% 0.21/0.51        | (v2_struct_0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '50'])).
% 0.21/0.51  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_C)
% 0.21/0.51        | ((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.21/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.21/0.51      inference('clc', [status(thm)], ['51', '52'])).
% 0.21/0.51  thf('54', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.21/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            (u1_struct_0 @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_A)
% 0.21/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.51            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))
% 0.21/0.51        | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '55', '56'])).
% 0.21/0.51  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B)
% 0.21/0.51        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.51            = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.51         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ sk_D @ sk_B))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               sk_D @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '61'])).
% 0.21/0.51  thf('63', plain, ((m1_pre_topc @ sk_D @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t35_borsuk_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (![X29 : $i, X30 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X29 @ X30)
% 0.21/0.51          | (r1_tarski @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 0.21/0.51          | ~ (l1_pre_topc @ X30))),
% 0.21/0.51      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_C)
% 0.21/0.51        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.51  thf('66', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('67', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_E @ 
% 0.21/0.51        (k1_zfmisc_1 @ 
% 0.21/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t38_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.51       ( ( r1_tarski @ C @ A ) =>
% 0.21/0.51         ( ( ( m1_subset_1 @
% 0.21/0.51               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.21/0.51               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.21/0.51             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.21/0.51             ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) ) | 
% 0.21/0.51           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_2, axiom,
% 0.21/0.51    (![B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.21/0.51       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_4, axiom,
% 0.21/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_0 @ D @ C @ B @ A ) =>
% 0.21/0.51       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 0.21/0.51         ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 0.21/0.51           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_5, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( r1_tarski @ C @ A ) =>
% 0.21/0.51         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ))).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.51          | (zip_tseitin_1 @ X8 @ X7)
% 0.21/0.51          | ~ (v1_funct_1 @ X9)
% 0.21/0.51          | ~ (v1_funct_2 @ X9 @ X7 @ X8)
% 0.21/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.21/0.51          | (zip_tseitin_0 @ X9 @ X6 @ X8 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ sk_E @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51           (u1_struct_0 @ sk_C))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.51          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ sk_E @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51           (u1_struct_0 @ sk_C))
% 0.21/0.51          | (zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (zip_tseitin_0 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.51           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((v1_funct_2 @ (k2_partfun1 @ X0 @ X1 @ X2 @ X3) @ X3 @ X1)
% 0.21/0.51          | ~ (zip_tseitin_0 @ X2 @ X3 @ X1 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (v1_funct_2 @ 
% 0.21/0.51           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            (u1_struct_0 @ sk_D)) @ 
% 0.21/0.51           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.21/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            (u1_struct_0 @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 0.21/0.51           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.51         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      ((~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 0.21/0.51           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['78', '81'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (((X4) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X4 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_B) = (k1_xboole_0)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.51  thf(fc2_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      (![X15 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.51          | ~ (l1_struct_0 @ X15)
% 0.21/0.51          | (v2_struct_0 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.51  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B))
% 0.21/0.51         <= (~
% 0.21/0.51             ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.51      inference('demod', [status(thm)], ['86', '87', '90'])).
% 0.21/0.51  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (zip_tseitin_0 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.51           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '73'])).
% 0.21/0.51  thf('95', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((v1_funct_1 @ (k2_partfun1 @ X0 @ X1 @ X2 @ X3))
% 0.21/0.51          | ~ (zip_tseitin_0 @ X2 @ X3 @ X1 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (v1_funct_1 @ 
% 0.21/0.51           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            (u1_struct_0 @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.21/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            (u1_struct_0 @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.51         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))
% 0.21/0.51         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)))
% 0.21/0.51         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.21/0.51         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['98', '101'])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (((X4) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X4 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.51  thf('104', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_B) = (k1_xboole_0)))
% 0.21/0.51         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      (![X15 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.51          | ~ (l1_struct_0 @ X15)
% 0.21/0.51          | (v2_struct_0 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('106', plain,
% 0.21/0.51      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.51         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.51  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.51  thf('109', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B))
% 0.21/0.51         <= (~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))))),
% 0.21/0.51      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.21/0.51  thf('110', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.51  thf('112', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (zip_tseitin_0 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.51           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '73'])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k2_partfun1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 0.21/0.51          | ~ (zip_tseitin_0 @ X2 @ X3 @ X1 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (m1_subset_1 @ 
% 0.21/0.51           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            (u1_struct_0 @ sk_D)) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.51  thf('115', plain,
% 0.21/0.51      (((k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D)
% 0.21/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.21/0.51            (u1_struct_0 @ sk_D)))),
% 0.21/0.51      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('116', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51        | (m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.51      inference('demod', [status(thm)], ['114', '115'])).
% 0.21/0.51  thf('117', plain,
% 0.21/0.51      (((k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.21/0.51         = (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D))),
% 0.21/0.51      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      ((~ (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('119', plain,
% 0.21/0.51      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.51  thf('120', plain,
% 0.21/0.51      (((zip_tseitin_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['116', '119'])).
% 0.21/0.51  thf('121', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (((X4) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X4 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.51  thf('122', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_B) = (k1_xboole_0)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['120', '121'])).
% 0.21/0.51  thf('123', plain,
% 0.21/0.51      (![X15 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.51          | ~ (l1_struct_0 @ X15)
% 0.21/0.51          | (v2_struct_0 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('124', plain,
% 0.21/0.51      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.51         | (v2_struct_0 @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['122', '123'])).
% 0.21/0.51  thf('125', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('126', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.51  thf('127', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_B))
% 0.21/0.51         <= (~
% 0.21/0.51             ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51               (k1_zfmisc_1 @ 
% 0.21/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 0.21/0.51      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.21/0.51  thf('128', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('129', plain,
% 0.21/0.51      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['127', '128'])).
% 0.21/0.51  thf('130', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ sk_D @ 
% 0.21/0.51         sk_B)) | 
% 0.21/0.51       ~
% 0.21/0.51       ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51         (k1_zfmisc_1 @ 
% 0.21/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))) | 
% 0.21/0.51       ~ ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E))) | 
% 0.21/0.51       ~
% 0.21/0.51       ((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.21/0.51         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['23'])).
% 0.21/0.51  thf('131', plain,
% 0.21/0.51      (~
% 0.21/0.51       ((v5_pre_topc @ (k3_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ sk_D @ 
% 0.21/0.51         sk_B))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['93', '111', '129', '130'])).
% 0.21/0.51  thf('132', plain,
% 0.21/0.51      (~ (v5_pre_topc @ (k2_tmap_1 @ sk_C @ sk_B @ sk_E @ sk_D) @ sk_D @ sk_B)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['62', '131'])).
% 0.21/0.51  thf('133', plain,
% 0.21/0.51      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '132'])).
% 0.21/0.51  thf('134', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('135', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.21/0.51      inference('clc', [status(thm)], ['133', '134'])).
% 0.21/0.51  thf('136', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('137', plain, ((v2_struct_0 @ sk_C)),
% 0.21/0.51      inference('clc', [status(thm)], ['135', '136'])).
% 0.21/0.51  thf('138', plain, ($false), inference('demod', [status(thm)], ['0', '137'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
