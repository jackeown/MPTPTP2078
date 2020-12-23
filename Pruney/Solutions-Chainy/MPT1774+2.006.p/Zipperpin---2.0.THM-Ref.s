%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jld8U2rHXN

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:17 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 476 expanded)
%              Number of leaves         :   34 ( 145 expanded)
%              Depth                    :   26
%              Number of atoms          : 2159 (19416 expanded)
%              Number of equality atoms :   16 ( 225 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t81_tmap_1,axiom,(
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
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( F = G )
                                  & ( m1_pre_topc @ D @ C )
                                  & ( r1_tmap_1 @ C @ B @ E @ F ) )
                               => ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ G ) ) ) ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X28 @ X31 )
      | ~ ( r1_tmap_1 @ X31 @ X27 @ X32 @ X30 )
      | ( X30 != X33 )
      | ( r1_tmap_1 @ X28 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('29',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X28 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32 ) @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X27 @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X28 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D_1 )
      | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D_1 @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D_1 @ X1 )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34'])).

thf('36',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
        | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['22','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
        | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
        | ( v2_struct_0 @ sk_D_1 )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['21','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_D_1 )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['25'])).

thf('61',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['20','59','60'])).

thf('62',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E ) @ sk_H ),
    inference(simpl_trail,[status(thm)],['16','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_tmap_1,axiom,(
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
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) )
                                   => ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( m1_connsp_2 @ F @ D @ G )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ~ ( m1_pre_topc @ X37 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r1_tmap_1 @ X37 @ X34 @ ( k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40 ) @ X39 )
      | ( r1_tmap_1 @ X35 @ X34 @ X40 @ X41 )
      | ( X41 != X39 )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X41 )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t83_tmap_1])).

thf('65',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_tarski @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_connsp_2 @ X38 @ X35 @ X39 )
      | ( r1_tmap_1 @ X35 @ X34 @ X40 @ X39 )
      | ~ ( r1_tmap_1 @ X37 @ X34 @ ( k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40 ) @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( m1_pre_topc @ X37 @ X35 )
      | ~ ( m1_pre_topc @ X35 @ X36 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X3 )
      | ~ ( m1_connsp_2 @ X2 @ sk_D_1 @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('77',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_D_1 @ sk_H )
      | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( v2_struct_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77','78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
    | ~ ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('83',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('84',plain,(
    m1_pre_topc @ sk_C @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
    | ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('92',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 )
      | ~ ( v3_pre_topc @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( v2_pre_topc @ sk_D_1 )
      | ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( v3_pre_topc @ sk_F @ sk_D_1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('96',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('97',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('102',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

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

thf('104',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ X18 @ X19 )
      | ( X18 != X16 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('105',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X19 @ X17 )
      | ( v3_pre_topc @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_F @ X0 )
      | ( v3_pre_topc @ sk_F @ sk_D_1 )
      | ~ ( m1_pre_topc @ sk_D_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_D_1 @ sk_B )
    | ( v3_pre_topc @ sk_F @ sk_D_1 )
    | ~ ( v3_pre_topc @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_D_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v3_pre_topc @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v3_pre_topc @ sk_F @ sk_D_1 ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D_1 ) ) )
      | ( m1_connsp_2 @ X0 @ sk_D_1 @ X1 )
      | ~ ( r1_tarski @ sk_F @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_F )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['94','100','101','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['83','112'])).

thf('114',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_F )
      | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      | ( v2_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H )
    | ~ ( r2_hidden @ sk_H @ sk_F ) ),
    inference('sup-',[status(thm)],['82','115'])).

thf('117',plain,(
    r2_hidden @ sk_G @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    r2_hidden @ sk_H @ sk_F ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H ) ),
    inference(demod,[status(thm)],['116','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    m1_connsp_2 @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ sk_H ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D_1 )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','122','123'])).

thf('125',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['49'])).

thf('126',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['15'])).

thf('129',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(split,[status(esa)],['19'])).

thf('132',plain,
    ( ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G )
    | ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['20','59','132'])).

thf('134',plain,(
    ~ ( r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H ) ),
    inference(simpl_trail,[status(thm)],['127','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_D_1 )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference(demod,[status(thm)],['0','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jld8U2rHXN
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 528 iterations in 0.262s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.55/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.74  thf(sk_F_type, type, sk_F: $i).
% 0.55/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.74  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.55/0.74  thf(sk_E_type, type, sk_E: $i).
% 0.55/0.74  thf(sk_H_type, type, sk_H: $i).
% 0.55/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.55/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(sk_G_type, type, sk_G: $i).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.55/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.74  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.55/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.74  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.55/0.74  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.55/0.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.55/0.74  thf(t85_tmap_1, conjecture,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.74             ( l1_pre_topc @ B ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.55/0.74               ( ![D:$i]:
% 0.55/0.74                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.55/0.74                   ( ![E:$i]:
% 0.55/0.74                     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.74                         ( v1_funct_2 @
% 0.55/0.74                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.55/0.74                         ( m1_subset_1 @
% 0.55/0.74                           E @ 
% 0.55/0.74                           ( k1_zfmisc_1 @
% 0.55/0.74                             ( k2_zfmisc_1 @
% 0.55/0.74                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.55/0.74                       ( ( m1_pre_topc @ C @ D ) =>
% 0.55/0.74                         ( ![F:$i]:
% 0.55/0.74                           ( ( m1_subset_1 @
% 0.55/0.74                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.55/0.74                             ( ![G:$i]:
% 0.55/0.74                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.74                                 ( ![H:$i]:
% 0.55/0.74                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.55/0.74                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.55/0.74                                         ( r2_hidden @ G @ F ) & 
% 0.55/0.74                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.55/0.74                                         ( ( G ) = ( H ) ) ) =>
% 0.55/0.74                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.55/0.74                                         ( r1_tmap_1 @
% 0.55/0.74                                           C @ A @ 
% 0.55/0.74                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.55/0.74                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i]:
% 0.55/0.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.55/0.74            ( l1_pre_topc @ A ) ) =>
% 0.55/0.74          ( ![B:$i]:
% 0.55/0.74            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.74                ( l1_pre_topc @ B ) ) =>
% 0.55/0.74              ( ![C:$i]:
% 0.55/0.74                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.55/0.74                  ( ![D:$i]:
% 0.55/0.74                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.55/0.74                      ( ![E:$i]:
% 0.55/0.74                        ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.74                            ( v1_funct_2 @
% 0.55/0.74                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.55/0.74                            ( m1_subset_1 @
% 0.55/0.74                              E @ 
% 0.55/0.74                              ( k1_zfmisc_1 @
% 0.55/0.74                                ( k2_zfmisc_1 @
% 0.55/0.74                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.55/0.74                          ( ( m1_pre_topc @ C @ D ) =>
% 0.55/0.74                            ( ![F:$i]:
% 0.55/0.74                              ( ( m1_subset_1 @
% 0.55/0.74                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.55/0.74                                ( ![G:$i]:
% 0.55/0.74                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.74                                    ( ![H:$i]:
% 0.55/0.74                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.55/0.74                                        ( ( ( v3_pre_topc @ F @ B ) & 
% 0.55/0.74                                            ( r2_hidden @ G @ F ) & 
% 0.55/0.74                                            ( r1_tarski @
% 0.55/0.74                                              F @ ( u1_struct_0 @ C ) ) & 
% 0.55/0.74                                            ( ( G ) = ( H ) ) ) =>
% 0.55/0.74                                          ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.55/0.74                                            ( r1_tmap_1 @
% 0.55/0.74                                              C @ A @ 
% 0.55/0.74                                              ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.55/0.74                                              H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t85_tmap_1])).
% 0.55/0.74  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d10_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.74      inference('simplify', [status(thm)], ['2'])).
% 0.55/0.74  thf(t3_subset, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (![X3 : $i, X5 : $i]:
% 0.55/0.74         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.55/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.74  thf('5', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['3', '4'])).
% 0.55/0.74  thf(t39_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_pre_topc @ B @ A ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.55/0.74               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X13 @ X14)
% 0.55/0.74          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.55/0.74          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.55/0.74          | ~ (l1_pre_topc @ X14))),
% 0.55/0.74      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X1)
% 0.55/0.74          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.55/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_D_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '7'])).
% 0.55/0.74  thf('9', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(dt_m1_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (![X11 : $i, X12 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X11 @ X12)
% 0.55/0.74          | (l1_pre_topc @ X11)
% 0.55/0.74          | ~ (l1_pre_topc @ X12))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.55/0.74  thf('11', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.55/0.74  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('13', plain, ((l1_pre_topc @ sk_D_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '13'])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('16', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.55/0.74      inference('split', [status(esa)], ['15'])).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('18', plain, (((sk_G) = (sk_H))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.55/0.74      inference('demod', [status(thm)], ['17', '18'])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)) | 
% 0.55/0.74       ~
% 0.55/0.74       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.55/0.74      inference('split', [status(esa)], ['19'])).
% 0.55/0.74  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('22', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('24', plain, (((sk_G) = (sk_H))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.55/0.74      inference('demod', [status(thm)], ['23', '24'])).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('split', [status(esa)], ['25'])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_E @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t81_tmap_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.74             ( l1_pre_topc @ B ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.55/0.74               ( ![D:$i]:
% 0.55/0.74                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.74                   ( ![E:$i]:
% 0.55/0.74                     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.74                         ( v1_funct_2 @
% 0.55/0.74                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                         ( m1_subset_1 @
% 0.55/0.74                           E @ 
% 0.55/0.74                           ( k1_zfmisc_1 @
% 0.55/0.74                             ( k2_zfmisc_1 @
% 0.55/0.74                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74                       ( ![F:$i]:
% 0.55/0.74                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.55/0.74                           ( ![G:$i]:
% 0.55/0.74                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.74                               ( ( ( ( F ) = ( G ) ) & 
% 0.55/0.74                                   ( m1_pre_topc @ D @ C ) & 
% 0.55/0.74                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.55/0.74                                 ( r1_tmap_1 @
% 0.55/0.74                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.55/0.74                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X27)
% 0.55/0.74          | ~ (v2_pre_topc @ X27)
% 0.55/0.74          | ~ (l1_pre_topc @ X27)
% 0.55/0.74          | (v2_struct_0 @ X28)
% 0.55/0.74          | ~ (m1_pre_topc @ X28 @ X29)
% 0.55/0.74          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X31))
% 0.55/0.74          | ~ (m1_pre_topc @ X28 @ X31)
% 0.55/0.74          | ~ (r1_tmap_1 @ X31 @ X27 @ X32 @ X30)
% 0.55/0.74          | ((X30) != (X33))
% 0.55/0.74          | (r1_tmap_1 @ X28 @ X27 @ 
% 0.55/0.74             (k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32) @ X33)
% 0.55/0.74          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.55/0.74          | ~ (m1_subset_1 @ X32 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 0.55/0.74          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 0.55/0.74          | ~ (v1_funct_1 @ X32)
% 0.55/0.74          | ~ (m1_pre_topc @ X31 @ X29)
% 0.55/0.74          | (v2_struct_0 @ X31)
% 0.55/0.74          | ~ (l1_pre_topc @ X29)
% 0.55/0.74          | ~ (v2_pre_topc @ X29)
% 0.55/0.74          | (v2_struct_0 @ X29))),
% 0.55/0.74      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X29)
% 0.55/0.74          | ~ (v2_pre_topc @ X29)
% 0.55/0.74          | ~ (l1_pre_topc @ X29)
% 0.55/0.74          | (v2_struct_0 @ X31)
% 0.55/0.74          | ~ (m1_pre_topc @ X31 @ X29)
% 0.55/0.74          | ~ (v1_funct_1 @ X32)
% 0.55/0.74          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 0.55/0.74          | ~ (m1_subset_1 @ X32 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 0.55/0.74          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X28))
% 0.55/0.74          | (r1_tmap_1 @ X28 @ X27 @ 
% 0.55/0.74             (k3_tmap_1 @ X29 @ X27 @ X31 @ X28 @ X32) @ X33)
% 0.55/0.74          | ~ (r1_tmap_1 @ X31 @ X27 @ X32 @ X33)
% 0.55/0.74          | ~ (m1_pre_topc @ X28 @ X31)
% 0.55/0.74          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.55/0.74          | ~ (m1_pre_topc @ X28 @ X29)
% 0.55/0.74          | (v2_struct_0 @ X28)
% 0.55/0.74          | ~ (l1_pre_topc @ X27)
% 0.55/0.74          | ~ (v2_pre_topc @ X27)
% 0.55/0.74          | (v2_struct_0 @ X27))),
% 0.55/0.74      inference('simplify', [status(thm)], ['28'])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ X1)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.55/0.74          | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X2)
% 0.55/0.74          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.55/0.74             (k3_tmap_1 @ X1 @ sk_A @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.55/0.74               (u1_struct_0 @ sk_A))
% 0.55/0.74          | ~ (v1_funct_1 @ sk_E)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.55/0.74          | (v2_struct_0 @ sk_D_1)
% 0.55/0.74          | ~ (l1_pre_topc @ X1)
% 0.55/0.74          | ~ (v2_pre_topc @ X1)
% 0.55/0.74          | (v2_struct_0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['27', '29'])).
% 0.55/0.74  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ X1)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.55/0.74          | ~ (m1_pre_topc @ X0 @ sk_D_1)
% 0.55/0.74          | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X2)
% 0.55/0.74          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.55/0.74             (k3_tmap_1 @ X1 @ sk_A @ sk_D_1 @ X0 @ sk_E) @ X2)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D_1 @ X1)
% 0.55/0.74          | (v2_struct_0 @ sk_D_1)
% 0.55/0.74          | ~ (l1_pre_topc @ X1)
% 0.55/0.74          | ~ (v2_pre_topc @ X1)
% 0.55/0.74          | (v2_struct_0 @ X1))),
% 0.55/0.74      inference('demod', [status(thm)], ['30', '31', '32', '33', '34'])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      ((![X0 : $i, X1 : $i]:
% 0.55/0.74          ((v2_struct_0 @ X0)
% 0.55/0.74           | ~ (v2_pre_topc @ X0)
% 0.55/0.74           | ~ (l1_pre_topc @ X0)
% 0.55/0.74           | (v2_struct_0 @ sk_D_1)
% 0.55/0.74           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.55/0.74           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.55/0.74           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.55/0.74              (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.55/0.74           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.55/0.74           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.55/0.74           | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.74           | (v2_struct_0 @ X1)
% 0.55/0.74           | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['26', '35'])).
% 0.55/0.74  thf('37', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D_1))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('38', plain, (((sk_G) = (sk_H))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('39', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.55/0.74      inference('demod', [status(thm)], ['37', '38'])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      ((![X0 : $i, X1 : $i]:
% 0.55/0.74          ((v2_struct_0 @ X0)
% 0.55/0.74           | ~ (v2_pre_topc @ X0)
% 0.55/0.74           | ~ (l1_pre_topc @ X0)
% 0.55/0.74           | (v2_struct_0 @ sk_D_1)
% 0.55/0.74           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.55/0.74           | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ X1))
% 0.55/0.74           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.55/0.74              (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E) @ sk_H)
% 0.55/0.74           | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.55/0.74           | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.74           | (v2_struct_0 @ X1)
% 0.55/0.74           | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('demod', [status(thm)], ['36', '39'])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      ((![X0 : $i]:
% 0.55/0.74          ((v2_struct_0 @ sk_A)
% 0.55/0.74           | (v2_struct_0 @ sk_C)
% 0.55/0.74           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.55/0.74           | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.55/0.74           | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74              (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.55/0.74           | (v2_struct_0 @ sk_D_1)
% 0.55/0.74           | ~ (l1_pre_topc @ X0)
% 0.55/0.74           | ~ (v2_pre_topc @ X0)
% 0.55/0.74           | (v2_struct_0 @ X0)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['22', '40'])).
% 0.55/0.74  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('43', plain,
% 0.55/0.74      ((![X0 : $i]:
% 0.55/0.74          ((v2_struct_0 @ sk_A)
% 0.55/0.74           | (v2_struct_0 @ sk_C)
% 0.55/0.74           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.55/0.74           | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74              (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74           | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.55/0.74           | (v2_struct_0 @ sk_D_1)
% 0.55/0.74           | ~ (l1_pre_topc @ X0)
% 0.55/0.74           | ~ (v2_pre_topc @ X0)
% 0.55/0.74           | (v2_struct_0 @ X0)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('demod', [status(thm)], ['41', '42'])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | ~ (v2_pre_topc @ sk_B)
% 0.55/0.74         | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D_1)
% 0.55/0.74         | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.55/0.74         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74            (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74         | (v2_struct_0 @ sk_C)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['21', '43'])).
% 0.55/0.74  thf('45', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('46', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('47', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('48', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B)
% 0.55/0.74         | (v2_struct_0 @ sk_D_1)
% 0.55/0.74         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74            (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74         | (v2_struct_0 @ sk_C)
% 0.55/0.74         | (v2_struct_0 @ sk_A)))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.55/0.74  thf('49', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)
% 0.55/0.74        | ~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('50', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74           (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)))),
% 0.55/0.74      inference('split', [status(esa)], ['49'])).
% 0.55/0.74  thf('51', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_A)
% 0.55/0.74         | (v2_struct_0 @ sk_C)
% 0.55/0.74         | (v2_struct_0 @ sk_D_1)
% 0.55/0.74         | (v2_struct_0 @ sk_B)))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['48', '50'])).
% 0.55/0.74  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('53', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_C)))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['51', '52'])).
% 0.55/0.74  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('55', plain,
% 0.55/0.74      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D_1)))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('clc', [status(thm)], ['53', '54'])).
% 0.55/0.74  thf('56', plain, (~ (v2_struct_0 @ sk_C)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('57', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_D_1))
% 0.55/0.74         <= (~
% 0.55/0.74             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74               (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) & 
% 0.55/0.74             ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('clc', [status(thm)], ['55', '56'])).
% 0.55/0.74  thf('58', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('59', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.55/0.74       ~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.55/0.74      inference('sup-', [status(thm)], ['57', '58'])).
% 0.55/0.74  thf('60', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)) | 
% 0.55/0.74       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.55/0.74      inference('split', [status(esa)], ['25'])).
% 0.55/0.74  thf('61', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74         (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['20', '59', '60'])).
% 0.55/0.74  thf('62', plain,
% 0.55/0.74      ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.55/0.74        (k3_tmap_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C @ sk_E) @ sk_H)),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['16', '61'])).
% 0.55/0.74  thf('63', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_E @ 
% 0.55/0.74        (k1_zfmisc_1 @ 
% 0.55/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t83_tmap_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.55/0.74             ( l1_pre_topc @ B ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.55/0.74               ( ![D:$i]:
% 0.55/0.74                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.55/0.74                   ( ![E:$i]:
% 0.55/0.74                     ( ( ( v1_funct_1 @ E ) & 
% 0.55/0.74                         ( v1_funct_2 @
% 0.55/0.74                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.55/0.74                         ( m1_subset_1 @
% 0.55/0.74                           E @ 
% 0.55/0.74                           ( k1_zfmisc_1 @
% 0.55/0.74                             ( k2_zfmisc_1 @
% 0.55/0.74                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.55/0.74                       ( ( m1_pre_topc @ C @ D ) =>
% 0.55/0.74                         ( ![F:$i]:
% 0.55/0.74                           ( ( m1_subset_1 @
% 0.55/0.74                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.55/0.74                             ( ![G:$i]:
% 0.55/0.74                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.55/0.74                                 ( ![H:$i]:
% 0.55/0.74                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.55/0.74                                     ( ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.55/0.74                                         ( m1_connsp_2 @ F @ D @ G ) & 
% 0.55/0.74                                         ( ( G ) = ( H ) ) ) =>
% 0.55/0.74                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.55/0.74                                         ( r1_tmap_1 @
% 0.55/0.74                                           C @ B @ 
% 0.55/0.74                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.55/0.74                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('64', plain,
% 0.55/0.74      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, 
% 0.55/0.74         X41 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X34)
% 0.55/0.74          | ~ (v2_pre_topc @ X34)
% 0.55/0.74          | ~ (l1_pre_topc @ X34)
% 0.55/0.74          | (v2_struct_0 @ X35)
% 0.55/0.74          | ~ (m1_pre_topc @ X35 @ X36)
% 0.55/0.74          | ~ (m1_pre_topc @ X37 @ X35)
% 0.55/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.55/0.74          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.55/0.74          | ~ (r1_tmap_1 @ X37 @ X34 @ 
% 0.55/0.74               (k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40) @ X39)
% 0.55/0.74          | (r1_tmap_1 @ X35 @ X34 @ X40 @ X41)
% 0.55/0.74          | ((X41) != (X39))
% 0.55/0.74          | ~ (m1_connsp_2 @ X38 @ X35 @ X41)
% 0.55/0.74          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X37))
% 0.55/0.74          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X35))
% 0.55/0.74          | ~ (m1_subset_1 @ X40 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))))
% 0.55/0.74          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))
% 0.55/0.74          | ~ (v1_funct_1 @ X40)
% 0.55/0.74          | ~ (m1_pre_topc @ X37 @ X36)
% 0.55/0.74          | (v2_struct_0 @ X37)
% 0.55/0.74          | ~ (l1_pre_topc @ X36)
% 0.55/0.74          | ~ (v2_pre_topc @ X36)
% 0.55/0.74          | (v2_struct_0 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [t83_tmap_1])).
% 0.55/0.74  thf('65', plain,
% 0.55/0.74      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.55/0.74         ((v2_struct_0 @ X36)
% 0.55/0.74          | ~ (v2_pre_topc @ X36)
% 0.55/0.74          | ~ (l1_pre_topc @ X36)
% 0.55/0.74          | (v2_struct_0 @ X37)
% 0.55/0.74          | ~ (m1_pre_topc @ X37 @ X36)
% 0.55/0.74          | ~ (v1_funct_1 @ X40)
% 0.55/0.74          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))
% 0.55/0.74          | ~ (m1_subset_1 @ X40 @ 
% 0.55/0.74               (k1_zfmisc_1 @ 
% 0.55/0.74                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X34))))
% 0.55/0.74          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X35))
% 0.55/0.74          | ~ (r1_tarski @ X38 @ (u1_struct_0 @ X37))
% 0.55/0.74          | ~ (m1_connsp_2 @ X38 @ X35 @ X39)
% 0.55/0.74          | (r1_tmap_1 @ X35 @ X34 @ X40 @ X39)
% 0.55/0.74          | ~ (r1_tmap_1 @ X37 @ X34 @ 
% 0.55/0.74               (k3_tmap_1 @ X36 @ X34 @ X35 @ X37 @ X40) @ X39)
% 0.55/0.74          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X37))
% 0.55/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.55/0.74          | ~ (m1_pre_topc @ X37 @ X35)
% 0.55/0.74          | ~ (m1_pre_topc @ X35 @ X36)
% 0.55/0.74          | (v2_struct_0 @ X35)
% 0.55/0.74          | ~ (l1_pre_topc @ X34)
% 0.55/0.74          | ~ (v2_pre_topc @ X34)
% 0.55/0.74          | (v2_struct_0 @ X34))),
% 0.55/0.74      inference('simplify', [status(thm)], ['64'])).
% 0.55/0.74  thf('66', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_D_1)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.55/0.74          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.55/0.74               (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.55/0.74          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X3)
% 0.55/0.74          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.55/0.74          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.55/0.74          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ 
% 0.55/0.74               (u1_struct_0 @ sk_A))
% 0.55/0.74          | ~ (v1_funct_1 @ sk_E)
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.74          | (v2_struct_0 @ X1)
% 0.55/0.74          | ~ (l1_pre_topc @ X0)
% 0.55/0.74          | ~ (v2_pre_topc @ X0)
% 0.55/0.74          | (v2_struct_0 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['63', '65'])).
% 0.55/0.74  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('69', plain,
% 0.55/0.74      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_A))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('71', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_A)
% 0.55/0.74          | (v2_struct_0 @ sk_D_1)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ sk_D_1)
% 0.55/0.74          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.55/0.74          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.55/0.74               (k3_tmap_1 @ X0 @ sk_A @ sk_D_1 @ X1 @ sk_E) @ X3)
% 0.55/0.74          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ X3)
% 0.55/0.74          | ~ (m1_connsp_2 @ X2 @ sk_D_1 @ X3)
% 0.55/0.74          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.55/0.74          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D_1))
% 0.55/0.74          | ~ (m1_pre_topc @ X1 @ X0)
% 0.55/0.74          | (v2_struct_0 @ X1)
% 0.55/0.74          | ~ (l1_pre_topc @ X0)
% 0.55/0.74          | ~ (v2_pre_topc @ X0)
% 0.55/0.74          | (v2_struct_0 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.55/0.74  thf('72', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_B)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ sk_C)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.55/0.74          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))
% 0.55/0.74          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.55/0.74          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.55/0.74          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.55/0.74          | ~ (m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.55/0.74          | ~ (m1_pre_topc @ sk_C @ sk_D_1)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ sk_D_1)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['62', '71'])).
% 0.55/0.74  thf('73', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('75', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('76', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.55/0.74      inference('demod', [status(thm)], ['37', '38'])).
% 0.55/0.74  thf('77', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_C))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('79', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('80', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_B)
% 0.55/0.74          | (v2_struct_0 @ sk_C)
% 0.55/0.74          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.55/0.74          | ~ (m1_connsp_2 @ X0 @ sk_D_1 @ sk_H)
% 0.55/0.74          | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.55/0.74          | (v2_struct_0 @ sk_D_1)
% 0.55/0.74          | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)],
% 0.55/0.74                ['72', '73', '74', '75', '76', '77', '78', '79'])).
% 0.55/0.74  thf('81', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_D_1)
% 0.55/0.74        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.55/0.74        | ~ (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)
% 0.55/0.74        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.55/0.74        | (v2_struct_0 @ sk_C)
% 0.55/0.74        | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['14', '80'])).
% 0.55/0.74  thf('82', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_D_1))),
% 0.55/0.74      inference('demod', [status(thm)], ['37', '38'])).
% 0.55/0.74  thf('83', plain,
% 0.55/0.74      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '13'])).
% 0.55/0.74  thf('84', plain, ((m1_pre_topc @ sk_C @ sk_D_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('85', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('86', plain,
% 0.55/0.74      (![X3 : $i, X5 : $i]:
% 0.55/0.74         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.55/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.74  thf('87', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['85', '86'])).
% 0.55/0.74  thf('88', plain,
% 0.55/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X13 @ X14)
% 0.55/0.74          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.55/0.74          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.55/0.74          | ~ (l1_pre_topc @ X14))),
% 0.55/0.74      inference('cnf', [status(esa)], [t39_pre_topc])).
% 0.55/0.74  thf('89', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.55/0.74          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['87', '88'])).
% 0.55/0.74  thf('90', plain,
% 0.55/0.74      (((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_D_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['84', '89'])).
% 0.55/0.74  thf('91', plain, ((l1_pre_topc @ sk_D_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf('92', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.55/0.74      inference('demod', [status(thm)], ['90', '91'])).
% 0.55/0.74  thf(t8_connsp_2, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.55/0.74                 ( ?[D:$i]:
% 0.55/0.74                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.55/0.74                     ( v3_pre_topc @ D @ A ) & 
% 0.55/0.74                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('93', plain,
% 0.55/0.74      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.55/0.74          | ~ (r2_hidden @ X20 @ X23)
% 0.55/0.74          | ~ (r1_tarski @ X23 @ X22)
% 0.55/0.74          | ~ (v3_pre_topc @ X23 @ X21)
% 0.55/0.74          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.55/0.74          | (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.55/0.74          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.55/0.74          | ~ (l1_pre_topc @ X21)
% 0.55/0.74          | ~ (v2_pre_topc @ X21)
% 0.55/0.74          | (v2_struct_0 @ X21))),
% 0.55/0.74      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.55/0.74  thf('94', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_D_1)
% 0.55/0.74          | ~ (v2_pre_topc @ sk_D_1)
% 0.55/0.74          | ~ (l1_pre_topc @ sk_D_1)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.55/0.74          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.55/0.74          | ~ (v3_pre_topc @ sk_F @ sk_D_1)
% 0.55/0.74          | ~ (r1_tarski @ sk_F @ X0)
% 0.55/0.74          | ~ (r2_hidden @ X1 @ sk_F)
% 0.55/0.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['92', '93'])).
% 0.55/0.74  thf('95', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(cc1_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.74       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.55/0.74  thf('96', plain,
% 0.55/0.74      (![X9 : $i, X10 : $i]:
% 0.55/0.74         (~ (m1_pre_topc @ X9 @ X10)
% 0.55/0.74          | (v2_pre_topc @ X9)
% 0.55/0.74          | ~ (l1_pre_topc @ X10)
% 0.55/0.74          | ~ (v2_pre_topc @ X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.55/0.74  thf('97', plain,
% 0.55/0.74      ((~ (v2_pre_topc @ sk_B)
% 0.55/0.74        | ~ (l1_pre_topc @ sk_B)
% 0.55/0.74        | (v2_pre_topc @ sk_D_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['95', '96'])).
% 0.55/0.74  thf('98', plain, ((v2_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('100', plain, ((v2_pre_topc @ sk_D_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.55/0.74  thf('101', plain, ((l1_pre_topc @ sk_D_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf('102', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('103', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))),
% 0.55/0.74      inference('demod', [status(thm)], ['90', '91'])).
% 0.55/0.74  thf(t33_tops_2, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ![C:$i]:
% 0.55/0.74             ( ( m1_pre_topc @ C @ A ) =>
% 0.55/0.74               ( ( v3_pre_topc @ B @ A ) =>
% 0.55/0.74                 ( ![D:$i]:
% 0.55/0.74                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.55/0.74                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.74  thf('104', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.55/0.74          | ~ (v3_pre_topc @ X16 @ X17)
% 0.55/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.55/0.74          | (v3_pre_topc @ X18 @ X19)
% 0.55/0.74          | ((X18) != (X16))
% 0.55/0.74          | ~ (m1_pre_topc @ X19 @ X17)
% 0.55/0.74          | ~ (l1_pre_topc @ X17))),
% 0.55/0.74      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.55/0.74  thf('105', plain,
% 0.55/0.74      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X17)
% 0.55/0.74          | ~ (m1_pre_topc @ X19 @ X17)
% 0.55/0.74          | (v3_pre_topc @ X16 @ X19)
% 0.55/0.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.55/0.74          | ~ (v3_pre_topc @ X16 @ X17)
% 0.55/0.74          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.55/0.74      inference('simplify', [status(thm)], ['104'])).
% 0.55/0.74  thf('106', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.55/0.74          | ~ (v3_pre_topc @ sk_F @ X0)
% 0.55/0.74          | (v3_pre_topc @ sk_F @ sk_D_1)
% 0.55/0.74          | ~ (m1_pre_topc @ sk_D_1 @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['103', '105'])).
% 0.55/0.74  thf('107', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_B)
% 0.55/0.74        | ~ (m1_pre_topc @ sk_D_1 @ sk_B)
% 0.55/0.74        | (v3_pre_topc @ sk_F @ sk_D_1)
% 0.55/0.74        | ~ (v3_pre_topc @ sk_F @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['102', '106'])).
% 0.55/0.74  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('109', plain, ((m1_pre_topc @ sk_D_1 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('110', plain, ((v3_pre_topc @ sk_F @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('111', plain, ((v3_pre_topc @ sk_F @ sk_D_1)),
% 0.55/0.74      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.55/0.74  thf('112', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((v2_struct_0 @ sk_D_1)
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D_1)))
% 0.55/0.74          | (m1_connsp_2 @ X0 @ sk_D_1 @ X1)
% 0.55/0.74          | ~ (r1_tarski @ sk_F @ X0)
% 0.55/0.74          | ~ (r2_hidden @ X1 @ sk_F)
% 0.55/0.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.55/0.74      inference('demod', [status(thm)], ['94', '100', '101', '111'])).
% 0.55/0.74  thf('113', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.55/0.74          | ~ (r2_hidden @ X0 @ sk_F)
% 0.55/0.74          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))
% 0.55/0.74          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_D_1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['83', '112'])).
% 0.55/0.74  thf('114', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('115', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.55/0.74          | ~ (r2_hidden @ X0 @ sk_F)
% 0.55/0.74          | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ X0)
% 0.55/0.74          | (v2_struct_0 @ sk_D_1))),
% 0.55/0.74      inference('demod', [status(thm)], ['113', '114'])).
% 0.55/0.74  thf('116', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_D_1)
% 0.55/0.74        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)
% 0.55/0.74        | ~ (r2_hidden @ sk_H @ sk_F))),
% 0.55/0.74      inference('sup-', [status(thm)], ['82', '115'])).
% 0.55/0.74  thf('117', plain, ((r2_hidden @ sk_G @ sk_F)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('118', plain, (((sk_G) = (sk_H))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('119', plain, ((r2_hidden @ sk_H @ sk_F)),
% 0.55/0.74      inference('demod', [status(thm)], ['117', '118'])).
% 0.55/0.74  thf('120', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_D_1)
% 0.55/0.74        | (m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H))),
% 0.55/0.74      inference('demod', [status(thm)], ['116', '119'])).
% 0.55/0.74  thf('121', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('122', plain, ((m1_connsp_2 @ (u1_struct_0 @ sk_C) @ sk_D_1 @ sk_H)),
% 0.55/0.74      inference('clc', [status(thm)], ['120', '121'])).
% 0.55/0.74  thf('123', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.55/0.74      inference('simplify', [status(thm)], ['2'])).
% 0.55/0.74  thf('124', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_A)
% 0.55/0.74        | (v2_struct_0 @ sk_D_1)
% 0.55/0.74        | (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)
% 0.55/0.74        | (v2_struct_0 @ sk_C)
% 0.55/0.74        | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['81', '122', '123'])).
% 0.55/0.74  thf('125', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))
% 0.55/0.74         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.55/0.74      inference('split', [status(esa)], ['49'])).
% 0.55/0.74  thf('126', plain, (((sk_G) = (sk_H))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('127', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.55/0.74         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.55/0.74      inference('demod', [status(thm)], ['125', '126'])).
% 0.55/0.74  thf('128', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.55/0.74      inference('split', [status(esa)], ['15'])).
% 0.55/0.74  thf('129', plain, (((sk_G) = (sk_H))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('130', plain,
% 0.55/0.74      (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.55/0.74         <= (((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)))),
% 0.55/0.74      inference('demod', [status(thm)], ['128', '129'])).
% 0.55/0.74  thf('131', plain,
% 0.55/0.74      ((~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))
% 0.55/0.74         <= (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)))),
% 0.55/0.74      inference('split', [status(esa)], ['19'])).
% 0.55/0.74  thf('132', plain,
% 0.55/0.74      (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G)) | 
% 0.55/0.74       ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H))),
% 0.55/0.74      inference('sup-', [status(thm)], ['130', '131'])).
% 0.55/0.74  thf('133', plain, (~ ((r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_G))),
% 0.55/0.74      inference('sat_resolution*', [status(thm)], ['20', '59', '132'])).
% 0.55/0.74  thf('134', plain, (~ (r1_tmap_1 @ sk_D_1 @ sk_A @ sk_E @ sk_H)),
% 0.55/0.74      inference('simpl_trail', [status(thm)], ['127', '133'])).
% 0.55/0.74  thf('135', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_B)
% 0.55/0.74        | (v2_struct_0 @ sk_C)
% 0.55/0.74        | (v2_struct_0 @ sk_D_1)
% 0.55/0.74        | (v2_struct_0 @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['124', '134'])).
% 0.55/0.74  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('137', plain,
% 0.55/0.74      (((v2_struct_0 @ sk_D_1) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['135', '136'])).
% 0.55/0.74  thf('138', plain, (~ (v2_struct_0 @ sk_D_1)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('139', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.55/0.74      inference('clc', [status(thm)], ['137', '138'])).
% 0.55/0.74  thf('140', plain, (~ (v2_struct_0 @ sk_B)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('141', plain, ((v2_struct_0 @ sk_C)),
% 0.55/0.74      inference('clc', [status(thm)], ['139', '140'])).
% 0.55/0.74  thf('142', plain, ($false), inference('demod', [status(thm)], ['0', '141'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
