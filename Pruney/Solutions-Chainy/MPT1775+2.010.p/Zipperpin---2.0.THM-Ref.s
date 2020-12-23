%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bweKUJep9z

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:22 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 394 expanded)
%              Number of leaves         :   37 ( 124 expanded)
%              Depth                    :   32
%              Number of atoms          : 1967 (14260 expanded)
%              Number of equality atoms :   11 ( 179 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t86_tmap_1,conjecture,(
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
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                       => ( ( ( v1_tsep_1 @ C @ D )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('27',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['19'])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X21 @ X24 )
      | ~ ( r1_tmap_1 @ X24 @ X20 @ X25 @ X23 )
      | ( X23 != X26 )
      | ( r1_tmap_1 @ X21 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25 ) @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X21 @ X20 @ ( k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25 ) @ X26 )
      | ~ ( r1_tmap_1 @ X24 @ X20 @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X21 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_B )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['25','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['23'])).

thf('49',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['19'])).

thf('61',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['24','59','60'])).

thf('62',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['22','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tmap_1,axiom,(
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
                                   => ( ( ( v3_pre_topc @ F @ D )
                                        & ( r2_hidden @ G @ F )
                                        & ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                                        & ( G = H ) )
                                     => ( ( r1_tmap_1 @ D @ B @ E @ G )
                                      <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X34 )
      | ( X34 != X32 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r2_hidden @ X34 @ X31 )
      | ~ ( v3_pre_topc @ X31 @ X28 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X28 ) )
      | ~ ( v3_pre_topc @ X31 @ X28 )
      | ~ ( r2_hidden @ X32 @ X31 )
      | ~ ( r1_tarski @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X28 @ X27 @ X33 @ X32 )
      | ~ ( r1_tmap_1 @ X30 @ X27 @ ( k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33 ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ sk_D )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('78',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_D )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77','78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','80'])).

thf('82',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( X11
       != ( u1_struct_0 @ X9 ) )
      | ~ ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v3_pre_topc @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('84',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X9 ) @ X10 )
      | ~ ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('89',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('90',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('91',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['85','86','87','88','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','95'])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','96'])).

thf('98',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','103'])).

thf('105',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['23'])).

thf('106',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['24','59'])).

thf('107',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('109',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('112',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('113',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['110','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['0','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bweKUJep9z
% 0.14/0.37  % Computer   : n015.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 10:56:38 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.57  % Solved by: fo/fo7.sh
% 0.24/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.57  % done 124 iterations in 0.073s
% 0.24/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.57  % SZS output start Refutation
% 0.24/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.57  thf(sk_G_type, type, sk_G: $i).
% 0.24/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.57  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.24/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.24/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.57  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.24/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.24/0.57  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.24/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.24/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.24/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.57  thf(t86_tmap_1, conjecture,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.57       ( ![B:$i]:
% 0.24/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.24/0.57             ( l1_pre_topc @ B ) ) =>
% 0.24/0.57           ( ![C:$i]:
% 0.24/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.57               ( ![D:$i]:
% 0.24/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.57                   ( ![E:$i]:
% 0.24/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.57                         ( v1_funct_2 @
% 0.24/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.57                         ( m1_subset_1 @
% 0.24/0.57                           E @ 
% 0.24/0.57                           ( k1_zfmisc_1 @
% 0.24/0.57                             ( k2_zfmisc_1 @
% 0.24/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.57                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.24/0.57                         ( ![F:$i]:
% 0.24/0.57                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.24/0.57                             ( ![G:$i]:
% 0.24/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.24/0.57                                 ( ( ( F ) = ( G ) ) =>
% 0.24/0.57                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.24/0.57                                     ( r1_tmap_1 @
% 0.24/0.57                                       C @ B @ 
% 0.24/0.57                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.57    (~( ![A:$i]:
% 0.24/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.24/0.57            ( l1_pre_topc @ A ) ) =>
% 0.24/0.57          ( ![B:$i]:
% 0.24/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.24/0.57                ( l1_pre_topc @ B ) ) =>
% 0.24/0.57              ( ![C:$i]:
% 0.24/0.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.57                  ( ![D:$i]:
% 0.24/0.57                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.57                      ( ![E:$i]:
% 0.24/0.57                        ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.57                            ( v1_funct_2 @
% 0.24/0.57                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.57                            ( m1_subset_1 @
% 0.24/0.57                              E @ 
% 0.24/0.57                              ( k1_zfmisc_1 @
% 0.24/0.57                                ( k2_zfmisc_1 @
% 0.24/0.57                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.57                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.24/0.57                            ( ![F:$i]:
% 0.24/0.57                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.24/0.57                                ( ![G:$i]:
% 0.24/0.57                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.24/0.57                                    ( ( ( F ) = ( G ) ) =>
% 0.24/0.57                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.24/0.57                                        ( r1_tmap_1 @
% 0.24/0.57                                          C @ B @ 
% 0.24/0.57                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.24/0.57    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.24/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('2', plain, (((sk_F) = (sk_G))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.24/0.57  thf(d2_subset_1, axiom,
% 0.24/0.57    (![A:$i,B:$i]:
% 0.24/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.24/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.24/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.57  thf('4', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i]:
% 0.24/0.57         (~ (m1_subset_1 @ X0 @ X1)
% 0.24/0.57          | (r2_hidden @ X0 @ X1)
% 0.24/0.57          | (v1_xboole_0 @ X1))),
% 0.24/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.24/0.57  thf('5', plain,
% 0.24/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.24/0.57        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.57  thf(t2_tsep_1, axiom,
% 0.24/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.24/0.57  thf('6', plain,
% 0.24/0.57      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.24/0.57      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.24/0.57  thf(t35_borsuk_1, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( l1_pre_topc @ A ) =>
% 0.24/0.57       ( ![B:$i]:
% 0.24/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.57           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.24/0.57  thf('7', plain,
% 0.24/0.57      (![X15 : $i, X16 : $i]:
% 0.24/0.57         (~ (m1_pre_topc @ X15 @ X16)
% 0.24/0.57          | (r1_tarski @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.24/0.57          | ~ (l1_pre_topc @ X16))),
% 0.24/0.57      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.24/0.57  thf('8', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         (~ (l1_pre_topc @ X0)
% 0.24/0.57          | ~ (l1_pre_topc @ X0)
% 0.24/0.57          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.57  thf('9', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.24/0.57          | ~ (l1_pre_topc @ X0))),
% 0.24/0.57      inference('simplify', [status(thm)], ['8'])).
% 0.24/0.57  thf('10', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf(t1_tsep_1, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( l1_pre_topc @ A ) =>
% 0.24/0.57       ( ![B:$i]:
% 0.24/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.57           ( m1_subset_1 @
% 0.24/0.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.24/0.57  thf('11', plain,
% 0.24/0.57      (![X12 : $i, X13 : $i]:
% 0.24/0.57         (~ (m1_pre_topc @ X12 @ X13)
% 0.24/0.57          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.24/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.24/0.57          | ~ (l1_pre_topc @ X13))),
% 0.24/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.24/0.57  thf('12', plain,
% 0.24/0.57      ((~ (l1_pre_topc @ sk_D)
% 0.24/0.57        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.24/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.57  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf(dt_m1_pre_topc, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( l1_pre_topc @ A ) =>
% 0.24/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.24/0.57  thf('14', plain,
% 0.24/0.57      (![X6 : $i, X7 : $i]:
% 0.24/0.57         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.24/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.24/0.57  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.24/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.57  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 0.24/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.24/0.57  thf('18', plain,
% 0.24/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.24/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.24/0.57      inference('demod', [status(thm)], ['12', '17'])).
% 0.24/0.57  thf('19', plain,
% 0.24/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.24/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('20', plain,
% 0.24/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.24/0.57      inference('split', [status(esa)], ['19'])).
% 0.24/0.57  thf('21', plain, (((sk_F) = (sk_G))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('22', plain,
% 0.24/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.24/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.24/0.57  thf('23', plain,
% 0.24/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.24/0.57        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('24', plain,
% 0.24/0.57      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.24/0.57       ~
% 0.24/0.57       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.24/0.57      inference('split', [status(esa)], ['23'])).
% 0.24/0.57  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('26', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.24/0.57  thf('27', plain,
% 0.24/0.57      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('split', [status(esa)], ['19'])).
% 0.24/0.57  thf('28', plain,
% 0.24/0.57      ((m1_subset_1 @ sk_E @ 
% 0.24/0.57        (k1_zfmisc_1 @ 
% 0.24/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf(t81_tmap_1, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.57       ( ![B:$i]:
% 0.24/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.24/0.57             ( l1_pre_topc @ B ) ) =>
% 0.24/0.57           ( ![C:$i]:
% 0.24/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.57               ( ![D:$i]:
% 0.24/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.57                   ( ![E:$i]:
% 0.24/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.57                         ( v1_funct_2 @
% 0.24/0.57                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.57                         ( m1_subset_1 @
% 0.24/0.57                           E @ 
% 0.24/0.57                           ( k1_zfmisc_1 @
% 0.24/0.57                             ( k2_zfmisc_1 @
% 0.24/0.57                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.57                       ( ![F:$i]:
% 0.24/0.57                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.24/0.57                           ( ![G:$i]:
% 0.24/0.57                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.24/0.57                               ( ( ( ( F ) = ( G ) ) & 
% 0.24/0.57                                   ( m1_pre_topc @ D @ C ) & 
% 0.24/0.57                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.24/0.57                                 ( r1_tmap_1 @
% 0.24/0.57                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.24/0.57                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.57  thf('29', plain,
% 0.24/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.24/0.57         ((v2_struct_0 @ X20)
% 0.24/0.57          | ~ (v2_pre_topc @ X20)
% 0.24/0.57          | ~ (l1_pre_topc @ X20)
% 0.24/0.57          | (v2_struct_0 @ X21)
% 0.24/0.57          | ~ (m1_pre_topc @ X21 @ X22)
% 0.24/0.57          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.24/0.57          | ~ (m1_pre_topc @ X21 @ X24)
% 0.24/0.57          | ~ (r1_tmap_1 @ X24 @ X20 @ X25 @ X23)
% 0.24/0.57          | ((X23) != (X26))
% 0.24/0.57          | (r1_tmap_1 @ X21 @ X20 @ 
% 0.24/0.57             (k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25) @ X26)
% 0.24/0.57          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.24/0.57          | ~ (m1_subset_1 @ X25 @ 
% 0.24/0.57               (k1_zfmisc_1 @ 
% 0.24/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))))
% 0.24/0.57          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))
% 0.24/0.57          | ~ (v1_funct_1 @ X25)
% 0.24/0.57          | ~ (m1_pre_topc @ X24 @ X22)
% 0.24/0.57          | (v2_struct_0 @ X24)
% 0.24/0.57          | ~ (l1_pre_topc @ X22)
% 0.24/0.57          | ~ (v2_pre_topc @ X22)
% 0.24/0.57          | (v2_struct_0 @ X22))),
% 0.24/0.57      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.24/0.57  thf('30', plain,
% 0.24/0.57      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.24/0.57         ((v2_struct_0 @ X22)
% 0.24/0.57          | ~ (v2_pre_topc @ X22)
% 0.24/0.57          | ~ (l1_pre_topc @ X22)
% 0.24/0.57          | (v2_struct_0 @ X24)
% 0.24/0.57          | ~ (m1_pre_topc @ X24 @ X22)
% 0.24/0.57          | ~ (v1_funct_1 @ X25)
% 0.24/0.57          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))
% 0.24/0.57          | ~ (m1_subset_1 @ X25 @ 
% 0.24/0.57               (k1_zfmisc_1 @ 
% 0.24/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X20))))
% 0.24/0.57          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.24/0.57          | (r1_tmap_1 @ X21 @ X20 @ 
% 0.24/0.57             (k3_tmap_1 @ X22 @ X20 @ X24 @ X21 @ X25) @ X26)
% 0.24/0.57          | ~ (r1_tmap_1 @ X24 @ X20 @ X25 @ X26)
% 0.24/0.57          | ~ (m1_pre_topc @ X21 @ X24)
% 0.24/0.57          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.24/0.57          | ~ (m1_pre_topc @ X21 @ X22)
% 0.24/0.57          | (v2_struct_0 @ X21)
% 0.24/0.57          | ~ (l1_pre_topc @ X20)
% 0.24/0.57          | ~ (v2_pre_topc @ X20)
% 0.24/0.57          | (v2_struct_0 @ X20))),
% 0.24/0.57      inference('simplify', [status(thm)], ['29'])).
% 0.24/0.57  thf('31', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         ((v2_struct_0 @ sk_B)
% 0.24/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.24/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.24/0.57          | (v2_struct_0 @ X0)
% 0.24/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.24/0.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.24/0.57          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.24/0.57          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.24/0.57             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.24/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.24/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.24/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.24/0.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.24/0.57          | (v2_struct_0 @ sk_D)
% 0.24/0.57          | ~ (l1_pre_topc @ X1)
% 0.24/0.57          | ~ (v2_pre_topc @ X1)
% 0.24/0.57          | (v2_struct_0 @ X1))),
% 0.24/0.57      inference('sup-', [status(thm)], ['28', '30'])).
% 0.24/0.57  thf('32', plain, ((v2_pre_topc @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('34', plain,
% 0.24/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('36', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.57         ((v2_struct_0 @ sk_B)
% 0.24/0.57          | (v2_struct_0 @ X0)
% 0.24/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.24/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.24/0.57          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.24/0.57          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.24/0.57          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.24/0.57             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.24/0.57          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.24/0.57          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.24/0.57          | (v2_struct_0 @ sk_D)
% 0.24/0.57          | ~ (l1_pre_topc @ X1)
% 0.24/0.57          | ~ (v2_pre_topc @ X1)
% 0.24/0.57          | (v2_struct_0 @ X1))),
% 0.24/0.57      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.24/0.57  thf('37', plain,
% 0.24/0.57      ((![X0 : $i, X1 : $i]:
% 0.24/0.57          ((v2_struct_0 @ X0)
% 0.24/0.57           | ~ (v2_pre_topc @ X0)
% 0.24/0.57           | ~ (l1_pre_topc @ X0)
% 0.24/0.57           | (v2_struct_0 @ sk_D)
% 0.24/0.57           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.24/0.57           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.24/0.57           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.24/0.57              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.24/0.57           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.24/0.57           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.24/0.57           | ~ (m1_pre_topc @ X1 @ X0)
% 0.24/0.57           | (v2_struct_0 @ X1)
% 0.24/0.57           | (v2_struct_0 @ sk_B)))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['27', '36'])).
% 0.24/0.57  thf('38', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('39', plain,
% 0.24/0.57      ((![X0 : $i, X1 : $i]:
% 0.24/0.57          ((v2_struct_0 @ X0)
% 0.24/0.57           | ~ (v2_pre_topc @ X0)
% 0.24/0.57           | ~ (l1_pre_topc @ X0)
% 0.24/0.57           | (v2_struct_0 @ sk_D)
% 0.24/0.57           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.24/0.57           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.24/0.57           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.24/0.57              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.24/0.57           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.24/0.57           | ~ (m1_pre_topc @ X1 @ X0)
% 0.24/0.57           | (v2_struct_0 @ X1)
% 0.24/0.57           | (v2_struct_0 @ sk_B)))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.24/0.57  thf('40', plain,
% 0.24/0.57      ((![X0 : $i]:
% 0.24/0.57          ((v2_struct_0 @ sk_B)
% 0.24/0.57           | (v2_struct_0 @ sk_C)
% 0.24/0.57           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.24/0.57           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.24/0.57           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.24/0.57           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.24/0.57           | (v2_struct_0 @ sk_D)
% 0.24/0.57           | ~ (l1_pre_topc @ X0)
% 0.24/0.57           | ~ (v2_pre_topc @ X0)
% 0.24/0.57           | (v2_struct_0 @ X0)))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['26', '39'])).
% 0.24/0.57  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('42', plain,
% 0.24/0.57      ((![X0 : $i]:
% 0.24/0.57          ((v2_struct_0 @ sk_B)
% 0.24/0.57           | (v2_struct_0 @ sk_C)
% 0.24/0.57           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.24/0.57           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.24/0.57           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.24/0.57           | (v2_struct_0 @ sk_D)
% 0.24/0.57           | ~ (l1_pre_topc @ X0)
% 0.24/0.57           | ~ (v2_pre_topc @ X0)
% 0.24/0.57           | (v2_struct_0 @ X0)))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.24/0.57  thf('43', plain,
% 0.24/0.57      ((((v2_struct_0 @ sk_A)
% 0.24/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.24/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.24/0.57         | (v2_struct_0 @ sk_D)
% 0.24/0.57         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.24/0.57         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.24/0.57         | (v2_struct_0 @ sk_C)
% 0.24/0.57         | (v2_struct_0 @ sk_B)))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['25', '42'])).
% 0.24/0.57  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('46', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('47', plain,
% 0.24/0.57      ((((v2_struct_0 @ sk_A)
% 0.24/0.57         | (v2_struct_0 @ sk_D)
% 0.24/0.57         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.24/0.57         | (v2_struct_0 @ sk_C)
% 0.24/0.57         | (v2_struct_0 @ sk_B)))
% 0.24/0.57         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.24/0.57  thf('48', plain,
% 0.24/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.24/0.57         <= (~
% 0.24/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.24/0.57      inference('split', [status(esa)], ['23'])).
% 0.24/0.57  thf('49', plain, (((sk_F) = (sk_G))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('50', plain,
% 0.24/0.57      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.24/0.57         <= (~
% 0.24/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.24/0.57      inference('demod', [status(thm)], ['48', '49'])).
% 0.24/0.57  thf('51', plain,
% 0.24/0.57      ((((v2_struct_0 @ sk_B)
% 0.24/0.57         | (v2_struct_0 @ sk_C)
% 0.24/0.57         | (v2_struct_0 @ sk_D)
% 0.24/0.57         | (v2_struct_0 @ sk_A)))
% 0.24/0.57         <= (~
% 0.24/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.24/0.57             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['47', '50'])).
% 0.24/0.57  thf('52', plain, (~ (v2_struct_0 @ sk_D)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('53', plain,
% 0.24/0.57      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.24/0.57         <= (~
% 0.24/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.24/0.57             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.24/0.57  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('55', plain,
% 0.24/0.57      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.24/0.57         <= (~
% 0.24/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.24/0.57             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('clc', [status(thm)], ['53', '54'])).
% 0.24/0.57  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('57', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_C))
% 0.24/0.57         <= (~
% 0.24/0.57             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.24/0.57             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('clc', [status(thm)], ['55', '56'])).
% 0.24/0.57  thf('58', plain, (~ (v2_struct_0 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('59', plain,
% 0.24/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.24/0.57       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.24/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.24/0.57  thf('60', plain,
% 0.24/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.24/0.57       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.24/0.57      inference('split', [status(esa)], ['19'])).
% 0.24/0.57  thf('61', plain,
% 0.24/0.57      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.24/0.57      inference('sat_resolution*', [status(thm)], ['24', '59', '60'])).
% 0.24/0.57  thf('62', plain,
% 0.24/0.57      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.24/0.57        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.24/0.57      inference('simpl_trail', [status(thm)], ['22', '61'])).
% 0.24/0.57  thf('63', plain,
% 0.24/0.57      ((m1_subset_1 @ sk_E @ 
% 0.24/0.57        (k1_zfmisc_1 @ 
% 0.24/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf(t84_tmap_1, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.57       ( ![B:$i]:
% 0.24/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.24/0.57             ( l1_pre_topc @ B ) ) =>
% 0.24/0.57           ( ![C:$i]:
% 0.24/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.24/0.57               ( ![D:$i]:
% 0.24/0.57                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.24/0.57                   ( ![E:$i]:
% 0.24/0.57                     ( ( ( v1_funct_1 @ E ) & 
% 0.24/0.57                         ( v1_funct_2 @
% 0.24/0.57                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.57                         ( m1_subset_1 @
% 0.24/0.57                           E @ 
% 0.24/0.57                           ( k1_zfmisc_1 @
% 0.24/0.57                             ( k2_zfmisc_1 @
% 0.24/0.57                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.57                       ( ( m1_pre_topc @ C @ D ) =>
% 0.24/0.57                         ( ![F:$i]:
% 0.24/0.57                           ( ( m1_subset_1 @
% 0.24/0.57                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.24/0.57                             ( ![G:$i]:
% 0.24/0.57                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.24/0.57                                 ( ![H:$i]:
% 0.24/0.57                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.24/0.57                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.24/0.57                                         ( r2_hidden @ G @ F ) & 
% 0.24/0.57                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.24/0.57                                         ( ( G ) = ( H ) ) ) =>
% 0.24/0.57                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.24/0.57                                         ( r1_tmap_1 @
% 0.24/0.57                                           C @ B @ 
% 0.24/0.57                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.24/0.57                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.57  thf('64', plain,
% 0.24/0.57      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, 
% 0.24/0.57         X34 : $i]:
% 0.24/0.57         ((v2_struct_0 @ X27)
% 0.24/0.57          | ~ (v2_pre_topc @ X27)
% 0.24/0.57          | ~ (l1_pre_topc @ X27)
% 0.24/0.57          | (v2_struct_0 @ X28)
% 0.24/0.57          | ~ (m1_pre_topc @ X28 @ X29)
% 0.24/0.57          | ~ (m1_pre_topc @ X30 @ X28)
% 0.24/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.24/0.57          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.24/0.57          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.24/0.57               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.24/0.57          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X34)
% 0.24/0.57          | ((X34) != (X32))
% 0.24/0.57          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 0.24/0.57          | ~ (r2_hidden @ X34 @ X31)
% 0.24/0.57          | ~ (v3_pre_topc @ X31 @ X28)
% 0.24/0.57          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X28))
% 0.24/0.57          | ~ (m1_subset_1 @ X33 @ 
% 0.24/0.57               (k1_zfmisc_1 @ 
% 0.24/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.24/0.57          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.24/0.57          | ~ (v1_funct_1 @ X33)
% 0.24/0.57          | ~ (m1_pre_topc @ X30 @ X29)
% 0.24/0.57          | (v2_struct_0 @ X30)
% 0.24/0.57          | ~ (l1_pre_topc @ X29)
% 0.24/0.57          | ~ (v2_pre_topc @ X29)
% 0.24/0.57          | (v2_struct_0 @ X29))),
% 0.24/0.57      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.24/0.57  thf('65', plain,
% 0.24/0.57      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.24/0.57         ((v2_struct_0 @ X29)
% 0.24/0.57          | ~ (v2_pre_topc @ X29)
% 0.24/0.57          | ~ (l1_pre_topc @ X29)
% 0.24/0.57          | (v2_struct_0 @ X30)
% 0.24/0.57          | ~ (m1_pre_topc @ X30 @ X29)
% 0.24/0.57          | ~ (v1_funct_1 @ X33)
% 0.24/0.57          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.24/0.57          | ~ (m1_subset_1 @ X33 @ 
% 0.24/0.57               (k1_zfmisc_1 @ 
% 0.24/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 0.24/0.57          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X28))
% 0.24/0.57          | ~ (v3_pre_topc @ X31 @ X28)
% 0.24/0.57          | ~ (r2_hidden @ X32 @ X31)
% 0.24/0.57          | ~ (r1_tarski @ X31 @ (u1_struct_0 @ X30))
% 0.24/0.57          | (r1_tmap_1 @ X28 @ X27 @ X33 @ X32)
% 0.24/0.57          | ~ (r1_tmap_1 @ X30 @ X27 @ 
% 0.24/0.57               (k3_tmap_1 @ X29 @ X27 @ X28 @ X30 @ X33) @ X32)
% 0.24/0.57          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 0.24/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.24/0.57          | ~ (m1_pre_topc @ X30 @ X28)
% 0.24/0.57          | ~ (m1_pre_topc @ X28 @ X29)
% 0.24/0.57          | (v2_struct_0 @ X28)
% 0.24/0.57          | ~ (l1_pre_topc @ X27)
% 0.24/0.57          | ~ (v2_pre_topc @ X27)
% 0.24/0.57          | (v2_struct_0 @ X27))),
% 0.24/0.57      inference('simplify', [status(thm)], ['64'])).
% 0.24/0.57  thf('66', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.57         ((v2_struct_0 @ sk_B)
% 0.24/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.24/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.24/0.57          | (v2_struct_0 @ sk_D)
% 0.24/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.24/0.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.24/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.24/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.24/0.57          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.24/0.57          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.24/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.57          | ~ (r2_hidden @ X3 @ X2)
% 0.24/0.57          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.24/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.24/0.57          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.24/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.24/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.24/0.57          | (v2_struct_0 @ X1)
% 0.24/0.57          | ~ (l1_pre_topc @ X0)
% 0.24/0.57          | ~ (v2_pre_topc @ X0)
% 0.24/0.57          | (v2_struct_0 @ X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['63', '65'])).
% 0.24/0.57  thf('67', plain, ((v2_pre_topc @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('69', plain,
% 0.24/0.57      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('71', plain,
% 0.24/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.57         ((v2_struct_0 @ sk_B)
% 0.24/0.57          | (v2_struct_0 @ sk_D)
% 0.24/0.57          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.24/0.57          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.24/0.57          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.24/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.24/0.57          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.24/0.57               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.24/0.57          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.24/0.57          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.24/0.57          | ~ (r2_hidden @ X3 @ X2)
% 0.24/0.57          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.24/0.57          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.24/0.57          | ~ (m1_pre_topc @ X1 @ X0)
% 0.24/0.57          | (v2_struct_0 @ X1)
% 0.24/0.57          | ~ (l1_pre_topc @ X0)
% 0.24/0.57          | ~ (v2_pre_topc @ X0)
% 0.24/0.57          | (v2_struct_0 @ X0))),
% 0.24/0.57      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.24/0.57  thf('72', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((v2_struct_0 @ sk_A)
% 0.24/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.24/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.24/0.57          | (v2_struct_0 @ sk_C)
% 0.24/0.57          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.24/0.57          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.24/0.57          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.24/0.57          | ~ (r2_hidden @ sk_F @ X0)
% 0.24/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.24/0.57          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.24/0.57          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.24/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.24/0.57          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.24/0.57          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.24/0.57          | (v2_struct_0 @ sk_D)
% 0.24/0.57          | (v2_struct_0 @ sk_B))),
% 0.24/0.57      inference('sup-', [status(thm)], ['62', '71'])).
% 0.24/0.57  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('75', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('76', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('77', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.24/0.57  thf('78', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('80', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((v2_struct_0 @ sk_A)
% 0.24/0.57          | (v2_struct_0 @ sk_C)
% 0.24/0.57          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.24/0.57          | ~ (r2_hidden @ sk_F @ X0)
% 0.24/0.57          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.24/0.57          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.24/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.24/0.57          | (v2_struct_0 @ sk_D)
% 0.24/0.57          | (v2_struct_0 @ sk_B))),
% 0.24/0.57      inference('demod', [status(thm)],
% 0.24/0.57                ['72', '73', '74', '75', '76', '77', '78', '79'])).
% 0.24/0.57  thf('81', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_B)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.24/0.57        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.24/0.57        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.24/0.57        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | (v2_struct_0 @ sk_A))),
% 0.24/0.57      inference('sup-', [status(thm)], ['18', '80'])).
% 0.24/0.57  thf('82', plain,
% 0.24/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.24/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.24/0.57      inference('demod', [status(thm)], ['12', '17'])).
% 0.24/0.57  thf(t16_tsep_1, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.57       ( ![B:$i]:
% 0.24/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.57           ( ![C:$i]:
% 0.24/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.57               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.24/0.57                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.24/0.57                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.24/0.57  thf('83', plain,
% 0.24/0.57      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.24/0.57         (~ (m1_pre_topc @ X9 @ X10)
% 0.24/0.57          | ((X11) != (u1_struct_0 @ X9))
% 0.24/0.57          | ~ (v1_tsep_1 @ X9 @ X10)
% 0.24/0.57          | ~ (m1_pre_topc @ X9 @ X10)
% 0.24/0.57          | (v3_pre_topc @ X11 @ X10)
% 0.24/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.24/0.57          | ~ (l1_pre_topc @ X10)
% 0.24/0.57          | ~ (v2_pre_topc @ X10))),
% 0.24/0.57      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.24/0.57  thf('84', plain,
% 0.24/0.57      (![X9 : $i, X10 : $i]:
% 0.24/0.57         (~ (v2_pre_topc @ X10)
% 0.24/0.57          | ~ (l1_pre_topc @ X10)
% 0.24/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.24/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.24/0.57          | (v3_pre_topc @ (u1_struct_0 @ X9) @ X10)
% 0.24/0.57          | ~ (v1_tsep_1 @ X9 @ X10)
% 0.24/0.57          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.24/0.57      inference('simplify', [status(thm)], ['83'])).
% 0.24/0.57  thf('85', plain,
% 0.24/0.57      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.24/0.57        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.24/0.57        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.24/0.57        | ~ (l1_pre_topc @ sk_D)
% 0.24/0.57        | ~ (v2_pre_topc @ sk_D))),
% 0.24/0.57      inference('sup-', [status(thm)], ['82', '84'])).
% 0.24/0.57  thf('86', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('87', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('88', plain, ((l1_pre_topc @ sk_D)),
% 0.24/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.24/0.57  thf('89', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf(cc1_pre_topc, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.24/0.57  thf('90', plain,
% 0.24/0.57      (![X3 : $i, X4 : $i]:
% 0.24/0.57         (~ (m1_pre_topc @ X3 @ X4)
% 0.24/0.57          | (v2_pre_topc @ X3)
% 0.24/0.57          | ~ (l1_pre_topc @ X4)
% 0.24/0.57          | ~ (v2_pre_topc @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.24/0.57  thf('91', plain,
% 0.24/0.57      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.24/0.57      inference('sup-', [status(thm)], ['89', '90'])).
% 0.24/0.57  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('94', plain, ((v2_pre_topc @ sk_D)),
% 0.24/0.57      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.24/0.57  thf('95', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.24/0.57      inference('demod', [status(thm)], ['85', '86', '87', '88', '94'])).
% 0.24/0.57  thf('96', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_B)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.24/0.57        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.24/0.57        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | (v2_struct_0 @ sk_A))),
% 0.24/0.57      inference('demod', [status(thm)], ['81', '95'])).
% 0.24/0.57  thf('97', plain,
% 0.24/0.57      ((~ (l1_pre_topc @ sk_C)
% 0.24/0.57        | (v2_struct_0 @ sk_A)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.24/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (v2_struct_0 @ sk_B))),
% 0.24/0.57      inference('sup-', [status(thm)], ['9', '96'])).
% 0.24/0.57  thf('98', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('99', plain,
% 0.24/0.57      (![X6 : $i, X7 : $i]:
% 0.24/0.57         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.24/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.24/0.57  thf('100', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.24/0.57      inference('sup-', [status(thm)], ['98', '99'])).
% 0.24/0.57  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('102', plain, ((l1_pre_topc @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['100', '101'])).
% 0.24/0.57  thf('103', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_A)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.24/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (v2_struct_0 @ sk_B))),
% 0.24/0.57      inference('demod', [status(thm)], ['97', '102'])).
% 0.24/0.57  thf('104', plain,
% 0.24/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.24/0.57        | (v2_struct_0 @ sk_B)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | (v2_struct_0 @ sk_A))),
% 0.24/0.57      inference('sup-', [status(thm)], ['5', '103'])).
% 0.24/0.57  thf('105', plain,
% 0.24/0.57      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.24/0.57         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.24/0.57      inference('split', [status(esa)], ['23'])).
% 0.24/0.57  thf('106', plain, (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.24/0.57      inference('sat_resolution*', [status(thm)], ['24', '59'])).
% 0.24/0.57  thf('107', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.24/0.57      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.24/0.57  thf('108', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_A)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (v2_struct_0 @ sk_B)
% 0.24/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['104', '107'])).
% 0.24/0.57  thf(fc2_struct_0, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.24/0.57       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.57  thf('109', plain,
% 0.24/0.57      (![X8 : $i]:
% 0.24/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.24/0.57          | ~ (l1_struct_0 @ X8)
% 0.24/0.57          | (v2_struct_0 @ X8))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.24/0.57  thf('110', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_B)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | (v2_struct_0 @ sk_A)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | ~ (l1_struct_0 @ sk_C))),
% 0.24/0.57      inference('sup-', [status(thm)], ['108', '109'])).
% 0.24/0.57  thf('111', plain, ((l1_pre_topc @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['100', '101'])).
% 0.24/0.57  thf(dt_l1_pre_topc, axiom,
% 0.24/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.57  thf('112', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.24/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.57  thf('113', plain, ((l1_struct_0 @ sk_C)),
% 0.24/0.57      inference('sup-', [status(thm)], ['111', '112'])).
% 0.24/0.57  thf('114', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_B)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | (v2_struct_0 @ sk_A)
% 0.24/0.57        | (v2_struct_0 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['110', '113'])).
% 0.24/0.57  thf('115', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_A)
% 0.24/0.57        | (v2_struct_0 @ sk_C)
% 0.24/0.57        | (v2_struct_0 @ sk_D)
% 0.24/0.57        | (v2_struct_0 @ sk_B))),
% 0.24/0.57      inference('simplify', [status(thm)], ['114'])).
% 0.24/0.57  thf('116', plain, (~ (v2_struct_0 @ sk_D)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('117', plain,
% 0.24/0.57      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.24/0.57      inference('sup-', [status(thm)], ['115', '116'])).
% 0.24/0.57  thf('118', plain, (~ (v2_struct_0 @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('119', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.24/0.57      inference('clc', [status(thm)], ['117', '118'])).
% 0.24/0.57  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('121', plain, ((v2_struct_0 @ sk_C)),
% 0.24/0.57      inference('clc', [status(thm)], ['119', '120'])).
% 0.24/0.57  thf('122', plain, ($false), inference('demod', [status(thm)], ['0', '121'])).
% 0.24/0.57  
% 0.24/0.57  % SZS output end Refutation
% 0.24/0.57  
% 0.24/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
