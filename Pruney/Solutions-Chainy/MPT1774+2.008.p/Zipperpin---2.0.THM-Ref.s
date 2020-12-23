%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hwJvYN22WJ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 865 expanded)
%              Number of leaves         :   35 ( 262 expanded)
%              Depth                    :   30
%              Number of atoms          : 2314 (35320 expanded)
%              Number of equality atoms :   29 ( 438 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t85_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( v3_pre_topc @ F @ B )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ A @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                     => ( ( ( v3_pre_topc @ F @ B )
                                          & ( r2_hidden @ G @ F )
                                          & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                          & ( G = H ) )
                                       => ( ( r1_tmap_1 @ D @ A @ E @ G )
                                        <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_F @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( ( k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) @ X25 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( k2_tmap_1 @ X19 @ X17 @ X20 @ X18 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ X20 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('46',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','49','50','51','52','53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( v3_pre_topc @ E @ B )
                                  & ( r2_hidden @ F @ E )
                                  & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( v3_pre_topc @ X31 @ X28 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( X30 != X32 )
      | ~ ( r1_tmap_1 @ X29 @ X33 @ ( k2_tmap_1 @ X28 @ X33 @ X34 @ X29 ) @ X32 )
      | ( r1_tmap_1 @ X28 @ X33 @ X34 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('71',plain,(
    ! [X28: $i,X29: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X28 @ X33 @ X34 @ X32 )
      | ~ ( r1_tmap_1 @ X29 @ X33 @ ( k2_tmap_1 @ X28 @ X33 @ X34 @ X29 ) @ X32 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X32 @ X31 )
      | ~ ( v3_pre_topc @ X31 @ X28 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('74',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('75',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( r2_hidden @ sk_H @ X0 )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
        | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ~ ( r2_hidden @ sk_H @ X0 )
        | ~ ( v3_pre_topc @ X0 @ sk_D )
        | ( v2_struct_0 @ sk_C )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['80','81','84','85'])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( r2_hidden @ sk_H @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['24','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ X15 @ X16 )
      | ( X15 != X13 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('91',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v3_pre_topc @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['87','97','100','101'])).

thf('103',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['6'])).

thf('104',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['2'])).

thf('114',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G ),
    inference('sat_resolution*',[status(thm)],['7','112','113'])).

thf('115',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H ),
    inference(simpl_trail,[status(thm)],['5','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('117',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( v3_pre_topc @ X31 @ X28 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X29 ) )
      | ( X30 != X32 )
      | ~ ( r1_tmap_1 @ X28 @ X33 @ X34 @ X30 )
      | ( r1_tmap_1 @ X29 @ X33 @ ( k2_tmap_1 @ X28 @ X33 @ X34 @ X29 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('119',plain,(
    ! [X28: $i,X29: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X29 @ X33 @ ( k2_tmap_1 @ X28 @ X33 @ X34 @ X29 ) @ X32 )
      | ~ ( r1_tmap_1 @ X28 @ X33 @ X34 @ X32 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X32 @ X31 )
      | ~ ( v3_pre_topc @ X31 @ X28 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('122',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('123',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( v3_pre_topc @ sk_F @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['116','127'])).

thf('129',plain,(
    v3_pre_topc @ sk_F @ sk_D ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ sk_H @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('133',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['98','99'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['6'])).

thf('140',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('141',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sat_resolution*',[status(thm)],['7','112'])).

thf('143',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    $false ),
    inference(demod,[status(thm)],['0','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hwJvYN22WJ
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:14:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 124 iterations in 0.041s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.47  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(t85_tmap_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.47             ( l1_pre_topc @ B ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.47               ( ![D:$i]:
% 0.20/0.47                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.47                   ( ![E:$i]:
% 0.20/0.47                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.47                         ( v1_funct_2 @
% 0.20/0.47                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.47                         ( m1_subset_1 @
% 0.20/0.47                           E @ 
% 0.20/0.47                           ( k1_zfmisc_1 @
% 0.20/0.47                             ( k2_zfmisc_1 @
% 0.20/0.47                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.47                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.47                         ( ![F:$i]:
% 0.20/0.47                           ( ( m1_subset_1 @
% 0.20/0.47                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.47                             ( ![G:$i]:
% 0.20/0.47                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.47                                 ( ![H:$i]:
% 0.20/0.47                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.47                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.47                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.47                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.47                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.47                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.47                                         ( r1_tmap_1 @
% 0.20/0.47                                           C @ A @ 
% 0.20/0.47                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.47                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.47            ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.47                ( l1_pre_topc @ B ) ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.47                  ( ![D:$i]:
% 0.20/0.47                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.47                      ( ![E:$i]:
% 0.20/0.47                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.47                            ( v1_funct_2 @
% 0.20/0.47                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.47                            ( m1_subset_1 @
% 0.20/0.47                              E @ 
% 0.20/0.47                              ( k1_zfmisc_1 @
% 0.20/0.47                                ( k2_zfmisc_1 @
% 0.20/0.47                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.47                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.47                            ( ![F:$i]:
% 0.20/0.47                              ( ( m1_subset_1 @
% 0.20/0.47                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.47                                ( ![G:$i]:
% 0.20/0.47                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.47                                    ( ![H:$i]:
% 0.20/0.47                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.47                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.47                                            ( r2_hidden @ G @ F ) & 
% 0.20/0.47                                            ( r1_tarski @
% 0.20/0.47                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.47                                            ( ( G ) = ( H ) ) ) =>
% 0.20/0.47                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.47                                            ( r1_tmap_1 @
% 0.20/0.47                                              C @ A @ 
% 0.20/0.47                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.47                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.20/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.47        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.47         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('4', plain, (((sk_G) = (sk_H))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.47         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)
% 0.20/0.47        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (~
% 0.20/0.47       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)) | 
% 0.20/0.47       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t1_tsep_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.47           ( m1_subset_1 @
% 0.20/0.47             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X26 : $i, X27 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X26 @ X27)
% 0.20/0.47          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.20/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.47          | ~ (l1_pre_topc @ X27))),
% 0.20/0.47      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.47        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_m1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.47          | (l1_pre_topc @ X11)
% 0.20/0.47          | ~ (l1_pre_topc @ X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.47  thf('13', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.47      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.47  thf(t3_subset, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]:
% 0.20/0.47         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.47  thf('18', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf('19', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t1_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.47       ( r1_tarski @ A @ C ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.47          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.47          | (r1_tarski @ X0 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((r1_tarski @ sk_F @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X3 : $i, X5 : $i]:
% 0.20/0.47         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E @ 
% 0.20/0.47        (k1_zfmisc_1 @ 
% 0.20/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d5_tmap_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.47             ( l1_pre_topc @ B ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.47               ( ![D:$i]:
% 0.20/0.47                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.47                   ( ![E:$i]:
% 0.20/0.47                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.47                         ( v1_funct_2 @
% 0.20/0.47                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.47                         ( m1_subset_1 @
% 0.20/0.47                           E @ 
% 0.20/0.47                           ( k1_zfmisc_1 @
% 0.20/0.47                             ( k2_zfmisc_1 @
% 0.20/0.47                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.47                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.47                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                           ( k2_partfun1 @
% 0.20/0.47                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.47                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X21)
% 0.20/0.47          | ~ (v2_pre_topc @ X21)
% 0.20/0.47          | ~ (l1_pre_topc @ X21)
% 0.20/0.47          | ~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.47          | ~ (m1_pre_topc @ X22 @ X24)
% 0.20/0.47          | ((k3_tmap_1 @ X23 @ X21 @ X24 @ X22 @ X25)
% 0.20/0.47              = (k2_partfun1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21) @ 
% 0.20/0.47                 X25 @ (u1_struct_0 @ X22)))
% 0.20/0.47          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.47               (k1_zfmisc_1 @ 
% 0.20/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))))
% 0.20/0.47          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X21))
% 0.20/0.47          | ~ (v1_funct_1 @ X25)
% 0.20/0.47          | ~ (m1_pre_topc @ X24 @ X23)
% 0.20/0.47          | ~ (l1_pre_topc @ X23)
% 0.20/0.47          | ~ (v2_pre_topc @ X23)
% 0.20/0.47          | (v2_struct_0 @ X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.20/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.47          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.47          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X0)
% 0.20/0.47          | ~ (v2_pre_topc @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.47          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.20/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.47          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.47          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.20/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '34'])).
% 0.20/0.47  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.20/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.47            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.47        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '38'])).
% 0.20/0.47  thf('40', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E @ 
% 0.20/0.47        (k1_zfmisc_1 @ 
% 0.20/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d4_tmap_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.47             ( l1_pre_topc @ B ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.47                 ( m1_subset_1 @
% 0.20/0.47                   C @ 
% 0.20/0.47                   ( k1_zfmisc_1 @
% 0.20/0.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.47               ( ![D:$i]:
% 0.20/0.47                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.47                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.47                     ( k2_partfun1 @
% 0.20/0.47                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.47                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X17)
% 0.20/0.47          | ~ (v2_pre_topc @ X17)
% 0.20/0.47          | ~ (l1_pre_topc @ X17)
% 0.20/0.47          | ~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.47          | ((k2_tmap_1 @ X19 @ X17 @ X20 @ X18)
% 0.20/0.47              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17) @ 
% 0.20/0.47                 X20 @ (u1_struct_0 @ X18)))
% 0.20/0.47          | ~ (m1_subset_1 @ X20 @ 
% 0.20/0.47               (k1_zfmisc_1 @ 
% 0.20/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))))
% 0.20/0.47          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))
% 0.20/0.47          | ~ (v1_funct_1 @ X20)
% 0.20/0.47          | ~ (l1_pre_topc @ X19)
% 0.20/0.47          | ~ (v2_pre_topc @ X19)
% 0.20/0.47          | (v2_struct_0 @ X19))),
% 0.20/0.47      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_D)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.47  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc1_pre_topc, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i]:
% 0.20/0.47         (~ (m1_pre_topc @ X9 @ X10)
% 0.20/0.47          | (v2_pre_topc @ X9)
% 0.20/0.47          | ~ (l1_pre_topc @ X10)
% 0.20/0.47          | ~ (v2_pre_topc @ X10))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.47  thf('47', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('49', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.47  thf('50', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('51', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('55', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_D)
% 0.20/0.47          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.47              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['43', '49', '50', '51', '52', '53', '54'])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.47            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.47        | (v2_struct_0 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['40', '55'])).
% 0.20/0.47  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('58', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_D)
% 0.20/0.47        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.47            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.47               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.47      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.47  thf('59', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('60', plain,
% 0.20/0.47      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.47         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.20/0.47            (u1_struct_0 @ sk_C)))),
% 0.20/0.47      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.47  thf('61', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('62', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.47            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))
% 0.20/0.47        | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '60', '61'])).
% 0.20/0.47  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('64', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.47            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)))),
% 0.20/0.47      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.47  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('66', plain,
% 0.20/0.47      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.47         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['64', '65'])).
% 0.20/0.47  thf('67', plain,
% 0.20/0.47      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.20/0.47         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('68', plain,
% 0.20/0.47      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.47         sk_H))
% 0.20/0.47         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['66', '67'])).
% 0.20/0.47  thf('69', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E @ 
% 0.20/0.47        (k1_zfmisc_1 @ 
% 0.20/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t66_tmap_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.47             ( l1_pre_topc @ B ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.47                 ( m1_subset_1 @
% 0.20/0.47                   C @ 
% 0.20/0.47                   ( k1_zfmisc_1 @
% 0.20/0.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.47               ( ![D:$i]:
% 0.20/0.47                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.47                   ( ![E:$i]:
% 0.20/0.47                     ( ( m1_subset_1 @
% 0.20/0.47                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.47                       ( ![F:$i]:
% 0.20/0.47                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.47                           ( ![G:$i]:
% 0.20/0.47                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.47                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.20/0.47                                   ( r2_hidden @ F @ E ) & 
% 0.20/0.47                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.47                                   ( ( F ) = ( G ) ) ) =>
% 0.20/0.47                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.20/0.47                                   ( r1_tmap_1 @
% 0.20/0.47                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('70', plain,
% 0.20/0.47      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X28)
% 0.20/0.47          | ~ (v2_pre_topc @ X28)
% 0.20/0.47          | ~ (l1_pre_topc @ X28)
% 0.20/0.47          | (v2_struct_0 @ X29)
% 0.20/0.47          | ~ (m1_pre_topc @ X29 @ X28)
% 0.20/0.47          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.20/0.47          | ~ (v3_pre_topc @ X31 @ X28)
% 0.20/0.47          | ~ (r2_hidden @ X30 @ X31)
% 0.20/0.47          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X29))
% 0.20/0.47          | ((X30) != (X32))
% 0.20/0.47          | ~ (r1_tmap_1 @ X29 @ X33 @ (k2_tmap_1 @ X28 @ X33 @ X34 @ X29) @ 
% 0.20/0.47               X32)
% 0.20/0.47          | (r1_tmap_1 @ X28 @ X33 @ X34 @ X30)
% 0.20/0.47          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.20/0.47          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.47          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.47               (k1_zfmisc_1 @ 
% 0.20/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))))
% 0.20/0.47          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))
% 0.20/0.47          | ~ (v1_funct_1 @ X34)
% 0.20/0.47          | ~ (l1_pre_topc @ X33)
% 0.20/0.47          | ~ (v2_pre_topc @ X33)
% 0.20/0.47          | (v2_struct_0 @ X33))),
% 0.20/0.47      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.20/0.47  thf('71', plain,
% 0.20/0.47      (![X28 : $i, X29 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X33)
% 0.20/0.47          | ~ (v2_pre_topc @ X33)
% 0.20/0.47          | ~ (l1_pre_topc @ X33)
% 0.20/0.47          | ~ (v1_funct_1 @ X34)
% 0.20/0.47          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))
% 0.20/0.47          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.47               (k1_zfmisc_1 @ 
% 0.20/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))))
% 0.20/0.47          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.47          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.20/0.47          | (r1_tmap_1 @ X28 @ X33 @ X34 @ X32)
% 0.20/0.47          | ~ (r1_tmap_1 @ X29 @ X33 @ (k2_tmap_1 @ X28 @ X33 @ X34 @ X29) @ 
% 0.20/0.47               X32)
% 0.20/0.47          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X29))
% 0.20/0.47          | ~ (r2_hidden @ X32 @ X31)
% 0.20/0.47          | ~ (v3_pre_topc @ X31 @ X28)
% 0.20/0.47          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.20/0.47          | ~ (m1_pre_topc @ X29 @ X28)
% 0.20/0.47          | (v2_struct_0 @ X29)
% 0.20/0.47          | ~ (l1_pre_topc @ X28)
% 0.20/0.47          | ~ (v2_pre_topc @ X28)
% 0.20/0.47          | (v2_struct_0 @ X28))),
% 0.20/0.47      inference('simplify', [status(thm)], ['70'])).
% 0.20/0.47  thf('72', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_D)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.47          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.47          | ~ (r2_hidden @ X1 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.47               X1)
% 0.20/0.47          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['69', '71'])).
% 0.20/0.47  thf('73', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.47  thf('74', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('75', plain,
% 0.20/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('79', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.47          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.47          | ~ (r2_hidden @ X1 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.47               X1)
% 0.20/0.47          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['72', '73', '74', '75', '76', '77', '78'])).
% 0.20/0.47  thf('80', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          ((v2_struct_0 @ sk_A)
% 0.20/0.47           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.47           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.20/0.47           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.47           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.47           | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.47           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.47           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.47           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.47           | (v2_struct_0 @ sk_C)
% 0.20/0.47           | (v2_struct_0 @ sk_D)))
% 0.20/0.47         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['68', '79'])).
% 0.20/0.47  thf('81', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('82', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('83', plain, (((sk_G) = (sk_H))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('84', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.47  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('86', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          ((v2_struct_0 @ sk_A)
% 0.20/0.47           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.47           | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.47           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.47           | ~ (r2_hidden @ sk_H @ X0)
% 0.20/0.47           | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.20/0.47           | (v2_struct_0 @ sk_C)
% 0.20/0.47           | (v2_struct_0 @ sk_D)))
% 0.20/0.47         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('demod', [status(thm)], ['80', '81', '84', '85'])).
% 0.20/0.47  thf('87', plain,
% 0.20/0.47      ((((v2_struct_0 @ sk_D)
% 0.20/0.47         | (v2_struct_0 @ sk_C)
% 0.20/0.47         | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.47         | ~ (r2_hidden @ sk_H @ sk_F)
% 0.20/0.47         | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.47         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.47         | (v2_struct_0 @ sk_A)))
% 0.20/0.47         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '86'])).
% 0.20/0.47  thf('88', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('89', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf(t33_tops_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.47               ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.47                 ( ![D:$i]:
% 0.20/0.47                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.47                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('90', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.47          | ~ (v3_pre_topc @ X13 @ X14)
% 0.20/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.47          | (v3_pre_topc @ X15 @ X16)
% 0.20/0.47          | ((X15) != (X13))
% 0.20/0.47          | ~ (m1_pre_topc @ X16 @ X14)
% 0.20/0.47          | ~ (l1_pre_topc @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.20/0.47  thf('91', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ X14)
% 0.20/0.47          | ~ (m1_pre_topc @ X16 @ X14)
% 0.20/0.47          | (v3_pre_topc @ X13 @ X16)
% 0.20/0.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.47          | ~ (v3_pre_topc @ X13 @ X14)
% 0.20/0.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.47  thf('92', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.47          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.20/0.47          | (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.47          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.47          | ~ (l1_pre_topc @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['89', '91'])).
% 0.20/0.47  thf('93', plain,
% 0.20/0.47      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.47        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.47        | (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.47        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['88', '92'])).
% 0.20/0.47  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('96', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('97', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.20/0.47  thf('98', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('99', plain, (((sk_G) = (sk_H))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('100', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.47      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.47  thf('101', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('102', plain,
% 0.20/0.47      ((((v2_struct_0 @ sk_D)
% 0.20/0.47         | (v2_struct_0 @ sk_C)
% 0.20/0.47         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)
% 0.20/0.47         | (v2_struct_0 @ sk_A)))
% 0.20/0.47         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('demod', [status(thm)], ['87', '97', '100', '101'])).
% 0.20/0.47  thf('103', plain,
% 0.20/0.47      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))
% 0.20/0.47         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('104', plain, (((sk_G) = (sk_H))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('105', plain,
% 0.20/0.47      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H))
% 0.20/0.47         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)))),
% 0.20/0.47      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.47  thf('106', plain,
% 0.20/0.47      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.20/0.47         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.20/0.47             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['102', '105'])).
% 0.20/0.47  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('108', plain,
% 0.20/0.47      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.20/0.47         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.20/0.47             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('clc', [status(thm)], ['106', '107'])).
% 0.20/0.47  thf('109', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('110', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_C))
% 0.20/0.47         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) & 
% 0.20/0.47             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('clc', [status(thm)], ['108', '109'])).
% 0.20/0.47  thf('111', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('112', plain,
% 0.20/0.47      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.20/0.47       ~
% 0.20/0.47       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.47      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.47  thf('113', plain,
% 0.20/0.47      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G)) | 
% 0.20/0.47       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('114', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_G))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['7', '112', '113'])).
% 0.20/0.47  thf('115', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_H)),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['5', '114'])).
% 0.20/0.47  thf('116', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.47  thf('117', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E @ 
% 0.20/0.47        (k1_zfmisc_1 @ 
% 0.20/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('118', plain,
% 0.20/0.47      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X28)
% 0.20/0.47          | ~ (v2_pre_topc @ X28)
% 0.20/0.47          | ~ (l1_pre_topc @ X28)
% 0.20/0.47          | (v2_struct_0 @ X29)
% 0.20/0.47          | ~ (m1_pre_topc @ X29 @ X28)
% 0.20/0.47          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.20/0.47          | ~ (v3_pre_topc @ X31 @ X28)
% 0.20/0.47          | ~ (r2_hidden @ X30 @ X31)
% 0.20/0.47          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X29))
% 0.20/0.47          | ((X30) != (X32))
% 0.20/0.47          | ~ (r1_tmap_1 @ X28 @ X33 @ X34 @ X30)
% 0.20/0.47          | (r1_tmap_1 @ X29 @ X33 @ (k2_tmap_1 @ X28 @ X33 @ X34 @ X29) @ X32)
% 0.20/0.47          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.20/0.47          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.47          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.47               (k1_zfmisc_1 @ 
% 0.20/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))))
% 0.20/0.47          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))
% 0.20/0.47          | ~ (v1_funct_1 @ X34)
% 0.20/0.47          | ~ (l1_pre_topc @ X33)
% 0.20/0.47          | ~ (v2_pre_topc @ X33)
% 0.20/0.47          | (v2_struct_0 @ X33))),
% 0.20/0.47      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.20/0.47  thf('119', plain,
% 0.20/0.47      (![X28 : $i, X29 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X33)
% 0.20/0.47          | ~ (v2_pre_topc @ X33)
% 0.20/0.47          | ~ (l1_pre_topc @ X33)
% 0.20/0.47          | ~ (v1_funct_1 @ X34)
% 0.20/0.47          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))
% 0.20/0.47          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.47               (k1_zfmisc_1 @ 
% 0.20/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X33))))
% 0.20/0.47          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.20/0.47          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.20/0.47          | (r1_tmap_1 @ X29 @ X33 @ (k2_tmap_1 @ X28 @ X33 @ X34 @ X29) @ X32)
% 0.20/0.47          | ~ (r1_tmap_1 @ X28 @ X33 @ X34 @ X32)
% 0.20/0.47          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X29))
% 0.20/0.47          | ~ (r2_hidden @ X32 @ X31)
% 0.20/0.47          | ~ (v3_pre_topc @ X31 @ X28)
% 0.20/0.47          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.20/0.47          | ~ (m1_pre_topc @ X29 @ X28)
% 0.20/0.47          | (v2_struct_0 @ X29)
% 0.20/0.47          | ~ (l1_pre_topc @ X28)
% 0.20/0.47          | ~ (v2_pre_topc @ X28)
% 0.20/0.47          | (v2_struct_0 @ X28))),
% 0.20/0.47      inference('simplify', [status(thm)], ['118'])).
% 0.20/0.47  thf('120', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_D)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.47          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.47          | ~ (r2_hidden @ X1 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.47          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.47          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.47          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['117', '119'])).
% 0.20/0.47  thf('121', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.47  thf('122', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('123', plain,
% 0.20/0.47      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('124', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('127', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.47          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.20/0.47          | ~ (r2_hidden @ X1 @ X2)
% 0.20/0.47          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.47          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)],
% 0.20/0.47                ['120', '121', '122', '123', '124', '125', '126'])).
% 0.20/0.47  thf('128', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.47          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.47          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.47          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (r2_hidden @ X1 @ sk_F)
% 0.20/0.47          | ~ (v3_pre_topc @ sk_F @ sk_D)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['116', '127'])).
% 0.20/0.47  thf('129', plain, ((v3_pre_topc @ sk_F @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.20/0.47  thf('130', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.47          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.47          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.47          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.47          | ~ (r2_hidden @ X1 @ sk_F)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['128', '129'])).
% 0.20/0.47  thf('131', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))
% 0.20/0.47          | ~ (r2_hidden @ sk_H @ sk_F)
% 0.20/0.47          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.47          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.47             sk_H)
% 0.20/0.47          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['115', '130'])).
% 0.20/0.47  thf('132', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.47  thf('133', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.20/0.47      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.47  thf('134', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_D)
% 0.20/0.47          | (v2_struct_0 @ X0)
% 0.20/0.47          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.47          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.47          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.47             sk_H)
% 0.20/0.47          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X0))
% 0.20/0.47          | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.20/0.47  thf('135', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.20/0.47        | (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.47           sk_H)
% 0.20/0.47        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.47        | (v2_struct_0 @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '134'])).
% 0.20/0.47  thf('136', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('137', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('138', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_A)
% 0.20/0.47        | (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.47           sk_H)
% 0.20/0.47        | (v2_struct_0 @ sk_C)
% 0.20/0.47        | (v2_struct_0 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.20/0.47  thf('139', plain,
% 0.20/0.47      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))
% 0.20/0.47         <= (~
% 0.20/0.47             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('split', [status(esa)], ['6'])).
% 0.20/0.47  thf('140', plain,
% 0.20/0.47      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.47         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['64', '65'])).
% 0.20/0.47  thf('141', plain,
% 0.20/0.47      ((~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.47           sk_H))
% 0.20/0.47         <= (~
% 0.20/0.47             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.47      inference('demod', [status(thm)], ['139', '140'])).
% 0.20/0.47  thf('142', plain,
% 0.20/0.47      (~
% 0.20/0.47       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.47         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_H))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['7', '112'])).
% 0.20/0.47  thf('143', plain,
% 0.20/0.47      (~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.47          sk_H)),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['141', '142'])).
% 0.20/0.47  thf('144', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['138', '143'])).
% 0.20/0.47  thf('145', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('146', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.20/0.47      inference('clc', [status(thm)], ['144', '145'])).
% 0.20/0.47  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('148', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.47      inference('clc', [status(thm)], ['146', '147'])).
% 0.20/0.47  thf('149', plain, ($false), inference('demod', [status(thm)], ['0', '148'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
