%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XrrvgENQ2p

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 379 expanded)
%              Number of leaves         :   36 ( 120 expanded)
%              Depth                    :   30
%              Number of atoms          : 1889 (13879 expanded)
%              Number of equality atoms :   13 ( 177 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('23',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_pre_topc @ X20 @ X23 )
      | ~ ( r1_tmap_1 @ X23 @ X19 @ X24 @ X22 )
      | ( X22 != X25 )
      | ( r1_tmap_1 @ X20 @ X19 @ ( k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X24 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X20 ) )
      | ( r1_tmap_1 @ X20 @ X19 @ ( k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X24 ) @ X25 )
      | ~ ( r1_tmap_1 @ X23 @ X19 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X20 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
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
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
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
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,
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
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
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
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
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
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
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
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['21','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['19'])).

thf('45',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('57',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['20','55','56'])).

thf('58',plain,(
    r1_tmap_1 @ sk_C @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['18','57'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tmap_1 @ X29 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32 ) @ X31 )
      | ( r1_tmap_1 @ X27 @ X26 @ X32 @ X33 )
      | ( X33 != X31 )
      | ~ ( r1_tarski @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X33 @ X30 )
      | ~ ( v3_pre_topc @ X30 @ X27 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t84_tmap_1])).

thf('61',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v3_pre_topc @ X30 @ X27 )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( r1_tarski @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( r1_tmap_1 @ X27 @ X26 @ X32 @ X31 )
      | ~ ( r1_tmap_1 @ X29 @ X26 @ ( k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
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
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
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
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
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
    inference(demod,[status(thm)],['68','69','70','71','72','73','74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','76'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('79',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','13'])).

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

thf('81',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D )
    | ~ ( l1_pre_topc @ sk_D )
    | ~ ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('87',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( v2_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('89',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['83','84','85','86','92'])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','79','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','94'])).

thf('96',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['19'])).

thf('97',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['20','55'])).

thf('98',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('100',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('104',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['104','105'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('107',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('108',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['101','108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['0','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XrrvgENQ2p
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 91 iterations in 0.053s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.22/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.52  thf(t86_tmap_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.52                         ( v1_funct_2 @
% 0.22/0.52                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.52                         ( m1_subset_1 @
% 0.22/0.52                           E @ 
% 0.22/0.52                           ( k1_zfmisc_1 @
% 0.22/0.52                             ( k2_zfmisc_1 @
% 0.22/0.52                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.52                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.52                         ( ![F:$i]:
% 0.22/0.52                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                             ( ![G:$i]:
% 0.22/0.52                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.52                                 ( ( ( F ) = ( G ) ) =>
% 0.22/0.52                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.22/0.52                                     ( r1_tmap_1 @
% 0.22/0.52                                       C @ B @ 
% 0.22/0.52                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52            ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52                ( l1_pre_topc @ B ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.52                  ( ![D:$i]:
% 0.22/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.52                      ( ![E:$i]:
% 0.22/0.52                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.52                            ( v1_funct_2 @
% 0.22/0.52                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.52                            ( m1_subset_1 @
% 0.22/0.52                              E @ 
% 0.22/0.52                              ( k1_zfmisc_1 @
% 0.22/0.52                                ( k2_zfmisc_1 @
% 0.22/0.52                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.52                          ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.52                            ( ![F:$i]:
% 0.22/0.52                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                                ( ![G:$i]:
% 0.22/0.52                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.52                                    ( ( ( F ) = ( G ) ) =>
% 0.22/0.52                                      ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.22/0.52                                        ( r1_tmap_1 @
% 0.22/0.52                                          C @ B @ 
% 0.22/0.52                                          ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t86_tmap_1])).
% 0.22/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain, (((sk_F) = (sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf(t2_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         ((r2_hidden @ X3 @ X4)
% 0.22/0.52          | (v1_xboole_0 @ X4)
% 0.22/0.52          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.22/0.52        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t1_tsep_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.52           ( m1_subset_1 @
% 0.22/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X14 @ X15)
% 0.22/0.52          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.52          | ~ (l1_pre_topc @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_m1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.52  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['8', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.22/0.52        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('17', plain, (((sk_F) = (sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.22/0.52        | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)) | 
% 0.22/0.52       ~
% 0.22/0.52       ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_E @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t81_tmap_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.52                         ( v1_funct_2 @
% 0.22/0.52                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.52                         ( m1_subset_1 @
% 0.22/0.52                           E @ 
% 0.22/0.52                           ( k1_zfmisc_1 @
% 0.22/0.52                             ( k2_zfmisc_1 @
% 0.22/0.52                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.52                       ( ![F:$i]:
% 0.22/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.52                           ( ![G:$i]:
% 0.22/0.52                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                               ( ( ( ( F ) = ( G ) ) & 
% 0.22/0.52                                   ( m1_pre_topc @ D @ C ) & 
% 0.22/0.52                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.22/0.52                                 ( r1_tmap_1 @
% 0.22/0.52                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.22/0.52                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X19)
% 0.22/0.52          | ~ (v2_pre_topc @ X19)
% 0.22/0.52          | ~ (l1_pre_topc @ X19)
% 0.22/0.52          | (v2_struct_0 @ X20)
% 0.22/0.52          | ~ (m1_pre_topc @ X20 @ X21)
% 0.22/0.52          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.22/0.52          | ~ (m1_pre_topc @ X20 @ X23)
% 0.22/0.52          | ~ (r1_tmap_1 @ X23 @ X19 @ X24 @ X22)
% 0.22/0.52          | ((X22) != (X25))
% 0.22/0.52          | (r1_tmap_1 @ X20 @ X19 @ 
% 0.22/0.52             (k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X24) @ X25)
% 0.22/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X20))
% 0.22/0.52          | ~ (m1_subset_1 @ X24 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))))
% 0.22/0.52          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))
% 0.22/0.52          | ~ (v1_funct_1 @ X24)
% 0.22/0.52          | ~ (m1_pre_topc @ X23 @ X21)
% 0.22/0.52          | (v2_struct_0 @ X23)
% 0.22/0.52          | ~ (l1_pre_topc @ X21)
% 0.22/0.52          | ~ (v2_pre_topc @ X21)
% 0.22/0.52          | (v2_struct_0 @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X21)
% 0.22/0.52          | ~ (v2_pre_topc @ X21)
% 0.22/0.52          | ~ (l1_pre_topc @ X21)
% 0.22/0.52          | (v2_struct_0 @ X23)
% 0.22/0.52          | ~ (m1_pre_topc @ X23 @ X21)
% 0.22/0.52          | ~ (v1_funct_1 @ X24)
% 0.22/0.52          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))
% 0.22/0.52          | ~ (m1_subset_1 @ X24 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X19))))
% 0.22/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X20))
% 0.22/0.52          | (r1_tmap_1 @ X20 @ X19 @ 
% 0.22/0.52             (k3_tmap_1 @ X21 @ X19 @ X23 @ X20 @ X24) @ X25)
% 0.22/0.52          | ~ (r1_tmap_1 @ X23 @ X19 @ X24 @ X25)
% 0.22/0.52          | ~ (m1_pre_topc @ X20 @ X23)
% 0.22/0.52          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.22/0.52          | ~ (m1_pre_topc @ X20 @ X21)
% 0.22/0.52          | (v2_struct_0 @ X20)
% 0.22/0.52          | ~ (l1_pre_topc @ X19)
% 0.22/0.52          | ~ (v2_pre_topc @ X19)
% 0.22/0.52          | (v2_struct_0 @ X19))),
% 0.22/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_B)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.22/0.52             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.52          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.22/0.52          | (v2_struct_0 @ sk_D)
% 0.22/0.52          | ~ (l1_pre_topc @ X1)
% 0.22/0.52          | ~ (v2_pre_topc @ X1)
% 0.22/0.52          | (v2_struct_0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '26'])).
% 0.22/0.52  thf('28', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('31', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_B)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X2)
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.22/0.52             (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ X2)
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.22/0.52          | (v2_struct_0 @ sk_D)
% 0.22/0.52          | ~ (l1_pre_topc @ X1)
% 0.22/0.52          | ~ (v2_pre_topc @ X1)
% 0.22/0.52          | (v2_struct_0 @ X1))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      ((![X0 : $i, X1 : $i]:
% 0.22/0.52          ((v2_struct_0 @ X0)
% 0.22/0.52           | ~ (v2_pre_topc @ X0)
% 0.22/0.52           | ~ (l1_pre_topc @ X0)
% 0.22/0.52           | (v2_struct_0 @ sk_D)
% 0.22/0.52           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.22/0.52           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.52              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.22/0.52           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.52           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.52           | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.52           | (v2_struct_0 @ X1)
% 0.22/0.52           | (v2_struct_0 @ sk_B)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '32'])).
% 0.22/0.52  thf('34', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      ((![X0 : $i, X1 : $i]:
% 0.22/0.52          ((v2_struct_0 @ X0)
% 0.22/0.52           | ~ (v2_pre_topc @ X0)
% 0.22/0.52           | ~ (l1_pre_topc @ X0)
% 0.22/0.52           | (v2_struct_0 @ sk_D)
% 0.22/0.52           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.22/0.52           | (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.52              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.22/0.52           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.52           | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.52           | (v2_struct_0 @ X1)
% 0.22/0.52           | (v2_struct_0 @ sk_B)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          ((v2_struct_0 @ sk_B)
% 0.22/0.52           | (v2_struct_0 @ sk_C)
% 0.22/0.52           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.22/0.52           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.52           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.52           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52           | (v2_struct_0 @ sk_D)
% 0.22/0.52           | ~ (l1_pre_topc @ X0)
% 0.22/0.52           | ~ (v2_pre_topc @ X0)
% 0.22/0.52           | (v2_struct_0 @ X0)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '35'])).
% 0.22/0.52  thf('37', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          ((v2_struct_0 @ sk_B)
% 0.22/0.52           | (v2_struct_0 @ sk_C)
% 0.22/0.52           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.22/0.52           | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52              (k3_tmap_1 @ X0 @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.52           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52           | (v2_struct_0 @ sk_D)
% 0.22/0.52           | ~ (l1_pre_topc @ X0)
% 0.22/0.52           | ~ (v2_pre_topc @ X0)
% 0.22/0.52           | (v2_struct_0 @ X0)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_A)
% 0.22/0.52         | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52         | (v2_struct_0 @ sk_D)
% 0.22/0.52         | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.22/0.52         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.52         | (v2_struct_0 @ sk_C)
% 0.22/0.52         | (v2_struct_0 @ sk_B)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '38'])).
% 0.22/0.52  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('42', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_A)
% 0.22/0.52         | (v2_struct_0 @ sk_D)
% 0.22/0.52         | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52            (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.52         | (v2_struct_0 @ sk_C)
% 0.22/0.52         | (v2_struct_0 @ sk_B)))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('45', plain, (((sk_F) = (sk_G))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_B)
% 0.22/0.52         | (v2_struct_0 @ sk_C)
% 0.22/0.52         | (v2_struct_0 @ sk_D)
% 0.22/0.52         | (v2_struct_0 @ sk_A)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.22/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['43', '46'])).
% 0.22/0.52  thf('48', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.22/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.52  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.22/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.52  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_C))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.22/0.52             ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('clc', [status(thm)], ['51', '52'])).
% 0.22/0.52  thf('54', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.22/0.52       ~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.22/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.22/0.52       ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['20', '55', '56'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      ((r1_tmap_1 @ sk_C @ sk_B @ 
% 0.22/0.52        (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['18', '57'])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_E @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t84_tmap_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.52                         ( v1_funct_2 @
% 0.22/0.52                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.52                         ( m1_subset_1 @
% 0.22/0.52                           E @ 
% 0.22/0.52                           ( k1_zfmisc_1 @
% 0.22/0.52                             ( k2_zfmisc_1 @
% 0.22/0.52                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.52                       ( ( m1_pre_topc @ C @ D ) =>
% 0.22/0.52                         ( ![F:$i]:
% 0.22/0.52                           ( ( m1_subset_1 @
% 0.22/0.52                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.22/0.52                             ( ![G:$i]:
% 0.22/0.52                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                                 ( ![H:$i]:
% 0.22/0.52                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.52                                     ( ( ( v3_pre_topc @ F @ D ) & 
% 0.22/0.52                                         ( r2_hidden @ G @ F ) & 
% 0.22/0.52                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.22/0.52                                         ( ( G ) = ( H ) ) ) =>
% 0.22/0.52                                       ( ( r1_tmap_1 @ D @ B @ E @ G ) <=>
% 0.22/0.52                                         ( r1_tmap_1 @
% 0.22/0.52                                           C @ B @ 
% 0.22/0.52                                           ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ 
% 0.22/0.52                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, 
% 0.22/0.52         X33 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X26)
% 0.22/0.52          | ~ (v2_pre_topc @ X26)
% 0.22/0.52          | ~ (l1_pre_topc @ X26)
% 0.22/0.52          | (v2_struct_0 @ X27)
% 0.22/0.52          | ~ (m1_pre_topc @ X27 @ X28)
% 0.22/0.52          | ~ (m1_pre_topc @ X29 @ X27)
% 0.22/0.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.22/0.52          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 0.22/0.52               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 0.22/0.52          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X33)
% 0.22/0.52          | ((X33) != (X31))
% 0.22/0.52          | ~ (r1_tarski @ X30 @ (u1_struct_0 @ X29))
% 0.22/0.52          | ~ (r2_hidden @ X33 @ X30)
% 0.22/0.52          | ~ (v3_pre_topc @ X30 @ X27)
% 0.22/0.52          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X27))
% 0.22/0.52          | ~ (m1_subset_1 @ X32 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.22/0.52          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.22/0.52          | ~ (v1_funct_1 @ X32)
% 0.22/0.52          | ~ (m1_pre_topc @ X29 @ X28)
% 0.22/0.52          | (v2_struct_0 @ X29)
% 0.22/0.52          | ~ (l1_pre_topc @ X28)
% 0.22/0.52          | ~ (v2_pre_topc @ X28)
% 0.22/0.52          | (v2_struct_0 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [t84_tmap_1])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X28)
% 0.22/0.52          | ~ (v2_pre_topc @ X28)
% 0.22/0.52          | ~ (l1_pre_topc @ X28)
% 0.22/0.52          | (v2_struct_0 @ X29)
% 0.22/0.52          | ~ (m1_pre_topc @ X29 @ X28)
% 0.22/0.52          | ~ (v1_funct_1 @ X32)
% 0.22/0.52          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.22/0.52          | ~ (m1_subset_1 @ X32 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X27))
% 0.22/0.52          | ~ (v3_pre_topc @ X30 @ X27)
% 0.22/0.52          | ~ (r2_hidden @ X31 @ X30)
% 0.22/0.52          | ~ (r1_tarski @ X30 @ (u1_struct_0 @ X29))
% 0.22/0.52          | (r1_tmap_1 @ X27 @ X26 @ X32 @ X31)
% 0.22/0.52          | ~ (r1_tmap_1 @ X29 @ X26 @ 
% 0.22/0.52               (k3_tmap_1 @ X28 @ X26 @ X27 @ X29 @ X32) @ X31)
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.22/0.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.22/0.52          | ~ (m1_pre_topc @ X29 @ X27)
% 0.22/0.52          | ~ (m1_pre_topc @ X27 @ X28)
% 0.22/0.52          | (v2_struct_0 @ X27)
% 0.22/0.52          | ~ (l1_pre_topc @ X26)
% 0.22/0.52          | ~ (v2_pre_topc @ X26)
% 0.22/0.52          | (v2_struct_0 @ X26))),
% 0.22/0.52      inference('simplify', [status(thm)], ['60'])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_B)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.52          | (v2_struct_0 @ sk_D)
% 0.22/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.22/0.52          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.22/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.22/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.52          | ~ (r2_hidden @ X3 @ X2)
% 0.22/0.52          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.52          | (v2_struct_0 @ X1)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['59', '61'])).
% 0.22/0.52  thf('63', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('64', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_B)
% 0.22/0.52          | (v2_struct_0 @ sk_D)
% 0.22/0.52          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.22/0.52          | ~ (r1_tmap_1 @ X1 @ sk_B @ 
% 0.22/0.52               (k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E) @ X3)
% 0.22/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ X3)
% 0.22/0.52          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.52          | ~ (r2_hidden @ X3 @ X2)
% 0.22/0.52          | ~ (v3_pre_topc @ X2 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.52          | (v2_struct_0 @ X1)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_C)
% 0.22/0.52          | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (r2_hidden @ sk_F @ X0)
% 0.22/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.22/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.52          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['58', '67'])).
% 0.22/0.52  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('71', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('72', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('73', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('75', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_C)
% 0.22/0.52          | ~ (v3_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (r2_hidden @ sk_F @ X0)
% 0.22/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.22/0.52          | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.52          | (v2_struct_0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['68', '69', '70', '71', '72', '73', '74', '75'])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | (v2_struct_0 @ sk_D)
% 0.22/0.52        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.52        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.22/0.52        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.52        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '76'])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('79', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['78'])).
% 0.22/0.52  thf('80', plain,
% 0.22/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['8', '13'])).
% 0.22/0.52  thf(t16_tsep_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.52                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.22/0.52                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('81', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X11 @ X12)
% 0.22/0.52          | ((X13) != (u1_struct_0 @ X11))
% 0.22/0.52          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.22/0.52          | ~ (m1_pre_topc @ X11 @ X12)
% 0.22/0.52          | (v3_pre_topc @ X13 @ X12)
% 0.22/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.52          | ~ (l1_pre_topc @ X12)
% 0.22/0.52          | ~ (v2_pre_topc @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.22/0.52  thf('82', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (v2_pre_topc @ X12)
% 0.22/0.52          | ~ (l1_pre_topc @ X12)
% 0.22/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.22/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.52          | (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.22/0.52          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.22/0.52          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.22/0.52      inference('simplify', [status(thm)], ['81'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.52        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.22/0.52        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_D)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['80', '82'])).
% 0.22/0.52  thf('84', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('85', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('86', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('87', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X5 @ X6)
% 0.22/0.52          | (v2_pre_topc @ X5)
% 0.22/0.52          | ~ (l1_pre_topc @ X6)
% 0.22/0.52          | ~ (v2_pre_topc @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.52  thf('89', plain,
% 0.22/0.52      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.52  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('92', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.22/0.52  thf('93', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['83', '84', '85', '86', '92'])).
% 0.22/0.52  thf('94', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | (v2_struct_0 @ sk_D)
% 0.22/0.52        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.52        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['77', '79', '93'])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)
% 0.22/0.52        | (v2_struct_0 @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '94'])).
% 0.22/0.52  thf('96', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))
% 0.22/0.52         <= (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)))),
% 0.22/0.52      inference('split', [status(esa)], ['19'])).
% 0.22/0.52  thf('97', plain, (~ ((r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['20', '55'])).
% 0.22/0.52  thf('98', plain, (~ (r1_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_F)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['96', '97'])).
% 0.22/0.52  thf('99', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | (v2_struct_0 @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['95', '98'])).
% 0.22/0.52  thf(fc2_struct_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.52  thf('100', plain,
% 0.22/0.52      (![X10 : $i]:
% 0.22/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.22/0.52          | ~ (l1_struct_0 @ X10)
% 0.22/0.52          | (v2_struct_0 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.52  thf('101', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_B)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | ~ (l1_struct_0 @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['99', '100'])).
% 0.22/0.52  thf('102', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('103', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.52  thf('104', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['102', '103'])).
% 0.22/0.52  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('106', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.52      inference('demod', [status(thm)], ['104', '105'])).
% 0.22/0.52  thf(dt_l1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.52  thf('107', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.52  thf('108', plain, ((l1_struct_0 @ sk_C)),
% 0.22/0.52      inference('sup-', [status(thm)], ['106', '107'])).
% 0.22/0.52  thf('109', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_B)
% 0.22/0.52        | (v2_struct_0 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['101', '108'])).
% 0.22/0.52  thf('110', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | (v2_struct_0 @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_C)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['109'])).
% 0.22/0.52  thf('111', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('112', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['110', '111'])).
% 0.22/0.52  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('114', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['112', '113'])).
% 0.22/0.52  thf('115', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('116', plain, ((v2_struct_0 @ sk_C)),
% 0.22/0.52      inference('clc', [status(thm)], ['114', '115'])).
% 0.22/0.52  thf('117', plain, ($false), inference('demod', [status(thm)], ['0', '116'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
