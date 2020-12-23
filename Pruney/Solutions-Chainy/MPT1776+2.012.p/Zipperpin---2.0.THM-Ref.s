%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BkNvvoyjuR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 348 expanded)
%              Number of leaves         :   35 ( 111 expanded)
%              Depth                    :   30
%              Number of atoms          : 1848 (13529 expanded)
%              Number of equality atoms :   13 ( 167 expanded)
%              Maximal formula depth    :   33 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t87_tmap_1,conjecture,(
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
                     => ( ( ( v1_tsep_1 @ C @ B )
                          & ( m1_pre_topc @ C @ B )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                       => ( ( ( v1_tsep_1 @ C @ B )
                            & ( m1_pre_topc @ C @ B )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
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
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('19',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( r1_tmap_1 @ X18 @ X14 @ X19 @ X17 )
      | ( X17 != X20 )
      | ( r1_tmap_1 @ X15 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19 ) @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X15 ) )
      | ( r1_tmap_1 @ X15 @ X14 @ ( k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19 ) @ X20 )
      | ~ ( r1_tmap_1 @ X18 @ X14 @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ~ ( l1_pre_topc @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
        | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ X1 @ sk_D )
        | ~ ( m1_pre_topc @ X1 @ X0 )
        | ( v2_struct_0 @ X1 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ~ ( m1_pre_topc @ sk_C @ sk_D )
        | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_C )
        | ~ ( m1_pre_topc @ sk_C @ X0 )
        | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
        | ~ ( m1_pre_topc @ sk_D @ X0 )
        | ( v2_struct_0 @ sk_D )
        | ~ ( l1_pre_topc @ X0 )
        | ~ ( v2_pre_topc @ X0 )
        | ( v2_struct_0 @ X0 ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['15'])).

thf('41',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('53',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['16','51','52'])).

thf('54',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['14','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_tmap_1,axiom,(
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

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_tmap_1 @ X23 @ X26 @ ( k3_tmap_1 @ X21 @ X26 @ X22 @ X23 @ X27 ) @ X25 )
      | ( r1_tmap_1 @ X22 @ X26 @ X27 @ X28 )
      | ( X28 != X25 )
      | ~ ( r1_tarski @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r2_hidden @ X28 @ X24 )
      | ~ ( v3_pre_topc @ X24 @ X21 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t85_tmap_1])).

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ~ ( v3_pre_topc @ X24 @ X21 )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( r1_tarski @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( r1_tmap_1 @ X22 @ X26 @ X27 @ X25 )
      | ~ ( r1_tmap_1 @ X23 @ X26 @ ( k3_tmap_1 @ X21 @ X26 @ X22 @ X23 @ X27 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X3 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ~ ( v3_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('68',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69','70','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','72'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('77',plain,(
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

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X9 ) @ X10 )
      | ~ ( v1_tsep_1 @ X9 @ X10 )
      | ~ ( m1_pre_topc @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ~ ( v1_tsep_1 @ sk_C @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_tsep_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','75','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','85'])).

thf('87',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('88',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['16','51'])).

thf('89',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('91',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('94',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['95','96'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('98',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('99',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['92','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['0','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BkNvvoyjuR
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:44:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 82 iterations in 0.050s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.51  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(t87_tmap_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.51                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.20/0.51                           ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.51                         ( ![F:$i]:
% 0.20/0.51                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                             ( ![G:$i]:
% 0.20/0.51                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.51                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.51                                     ( r1_tmap_1 @
% 0.20/0.51                                       C @ A @ 
% 0.20/0.51                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51                ( l1_pre_topc @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.51                      ( ![E:$i]:
% 0.20/0.51                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                            ( v1_funct_2 @
% 0.20/0.51                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.51                            ( m1_subset_1 @
% 0.20/0.51                              E @ 
% 0.20/0.51                              ( k1_zfmisc_1 @
% 0.20/0.51                                ( k2_zfmisc_1 @
% 0.20/0.51                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.51                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.20/0.51                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.51                            ( ![F:$i]:
% 0.20/0.51                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                                ( ![G:$i]:
% 0.20/0.51                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                                    ( ( ( F ) = ( G ) ) =>
% 0.20/0.51                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.51                                        ( r1_tmap_1 @
% 0.20/0.51                                          C @ A @ 
% 0.20/0.51                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.20/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ X3 @ X4)
% 0.20/0.51          | (v1_xboole_0 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.51        | (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t1_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( m1_subset_1 @
% 0.20/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.51          | ~ (l1_pre_topc @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.20/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('13', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.20/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.20/0.51       ~
% 0.20/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.51      inference('split', [status(esa)], ['15'])).
% 0.20/0.51  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t81_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51                       ( ![F:$i]:
% 0.20/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                           ( ![G:$i]:
% 0.20/0.51                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                               ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.51                                   ( m1_pre_topc @ D @ C ) & 
% 0.20/0.51                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.20/0.51                                 ( r1_tmap_1 @
% 0.20/0.51                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.51                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X14)
% 0.20/0.51          | ~ (v2_pre_topc @ X14)
% 0.20/0.51          | ~ (l1_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X15)
% 0.20/0.51          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.20/0.51          | ~ (m1_pre_topc @ X15 @ X18)
% 0.20/0.51          | ~ (r1_tmap_1 @ X18 @ X14 @ X19 @ X17)
% 0.20/0.51          | ((X17) != (X20))
% 0.20/0.51          | (r1_tmap_1 @ X15 @ X14 @ 
% 0.20/0.51             (k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19) @ X20)
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.20/0.51          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))))
% 0.20/0.51          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ~ (m1_pre_topc @ X18 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X18)
% 0.20/0.51          | ~ (l1_pre_topc @ X16)
% 0.20/0.51          | ~ (v2_pre_topc @ X16)
% 0.20/0.51          | (v2_struct_0 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X16)
% 0.20/0.51          | ~ (v2_pre_topc @ X16)
% 0.20/0.51          | ~ (l1_pre_topc @ X16)
% 0.20/0.51          | (v2_struct_0 @ X18)
% 0.20/0.51          | ~ (m1_pre_topc @ X18 @ X16)
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))
% 0.20/0.51          | ~ (m1_subset_1 @ X19 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X14))))
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X15))
% 0.20/0.51          | (r1_tmap_1 @ X15 @ X14 @ 
% 0.20/0.51             (k3_tmap_1 @ X16 @ X14 @ X18 @ X15 @ X19) @ X20)
% 0.20/0.51          | ~ (r1_tmap_1 @ X18 @ X14 @ X19 @ X20)
% 0.20/0.51          | ~ (m1_pre_topc @ X15 @ X18)
% 0.20/0.51          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.20/0.51          | ~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.51          | (v2_struct_0 @ X15)
% 0.20/0.51          | ~ (l1_pre_topc @ X14)
% 0.20/0.51          | ~ (v2_pre_topc @ X14)
% 0.20/0.51          | (v2_struct_0 @ X14))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.51          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.51             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ X1)
% 0.20/0.51          | ~ (v2_pre_topc @ X1)
% 0.20/0.51          | (v2_struct_0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '22'])).
% 0.20/0.51  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.51          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.51          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.20/0.51             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ X1)
% 0.20/0.51          | ~ (v2_pre_topc @ X1)
% 0.20/0.51          | (v2_struct_0 @ X1))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((![X0 : $i, X1 : $i]:
% 0.20/0.51          ((v2_struct_0 @ X0)
% 0.20/0.51           | ~ (v2_pre_topc @ X0)
% 0.20/0.51           | ~ (l1_pre_topc @ X0)
% 0.20/0.51           | (v2_struct_0 @ sk_D)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.51           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.51              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.20/0.51           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.51           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51           | (v2_struct_0 @ X1)
% 0.20/0.51           | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '28'])).
% 0.20/0.51  thf('30', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((![X0 : $i, X1 : $i]:
% 0.20/0.51          ((v2_struct_0 @ X0)
% 0.20/0.51           | ~ (v2_pre_topc @ X0)
% 0.20/0.51           | ~ (l1_pre_topc @ X0)
% 0.20/0.51           | (v2_struct_0 @ sk_D)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.51           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.20/0.51           | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.51              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.20/0.51           | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.51           | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51           | (v2_struct_0 @ X1)
% 0.20/0.51           | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((v2_struct_0 @ sk_A)
% 0.20/0.51           | (v2_struct_0 @ sk_C)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.51           | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.51           | (v2_struct_0 @ sk_D)
% 0.20/0.51           | ~ (l1_pre_topc @ X0)
% 0.20/0.51           | ~ (v2_pre_topc @ X0)
% 0.20/0.51           | (v2_struct_0 @ X0)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '31'])).
% 0.20/0.51  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((v2_struct_0 @ sk_A)
% 0.20/0.51           | (v2_struct_0 @ sk_C)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.51           | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51              (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.51           | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.51           | (v2_struct_0 @ sk_D)
% 0.20/0.51           | ~ (l1_pre_topc @ X0)
% 0.20/0.51           | ~ (v2_pre_topc @ X0)
% 0.20/0.51           | (v2_struct_0 @ X0)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B)
% 0.20/0.51         | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51         | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_D)
% 0.20/0.51         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.51         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.51         | (v2_struct_0 @ sk_C)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '34'])).
% 0.20/0.51  thf('36', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B)
% 0.20/0.51         | (v2_struct_0 @ sk_D)
% 0.20/0.51         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51            (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.20/0.51         | (v2_struct_0 @ sk_C)
% 0.20/0.51         | (v2_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.51      inference('split', [status(esa)], ['15'])).
% 0.20/0.51  thf('41', plain, (((sk_F) = (sk_G))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_A)
% 0.20/0.51         | (v2_struct_0 @ sk_C)
% 0.20/0.51         | (v2_struct_0 @ sk_D)
% 0.20/0.51         | (v2_struct_0 @ sk_B)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '42'])).
% 0.20/0.51  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.51  thf('46', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_D))
% 0.20/0.51         <= (~
% 0.20/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.51             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.20/0.51       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.20/0.51       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.51      inference('split', [status(esa)], ['11'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['16', '51', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.51        (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['14', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_E @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t85_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.51                   ( ![E:$i]:
% 0.20/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.51                         ( v1_funct_2 @
% 0.20/0.51                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.51                         ( m1_subset_1 @
% 0.20/0.51                           E @ 
% 0.20/0.51                           ( k1_zfmisc_1 @
% 0.20/0.51                             ( k2_zfmisc_1 @
% 0.20/0.51                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.51                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.51                         ( ![F:$i]:
% 0.20/0.51                           ( ( m1_subset_1 @
% 0.20/0.51                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.51                             ( ![G:$i]:
% 0.20/0.51                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.51                                 ( ![H:$i]:
% 0.20/0.51                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.51                                     ( ( ( v3_pre_topc @ F @ B ) & 
% 0.20/0.51                                         ( r2_hidden @ G @ F ) & 
% 0.20/0.51                                         ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.51                                         ( ( G ) = ( H ) ) ) =>
% 0.20/0.51                                       ( ( r1_tmap_1 @ D @ A @ E @ G ) <=>
% 0.20/0.51                                         ( r1_tmap_1 @
% 0.20/0.51                                           C @ A @ 
% 0.20/0.51                                           ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ 
% 0.20/0.51                                           H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, 
% 0.20/0.51         X28 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X21)
% 0.20/0.51          | ~ (v2_pre_topc @ X21)
% 0.20/0.51          | ~ (l1_pre_topc @ X21)
% 0.20/0.51          | (v2_struct_0 @ X22)
% 0.20/0.51          | ~ (m1_pre_topc @ X22 @ X21)
% 0.20/0.51          | ~ (m1_pre_topc @ X23 @ X22)
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.20/0.51          | ~ (r1_tmap_1 @ X23 @ X26 @ 
% 0.20/0.51               (k3_tmap_1 @ X21 @ X26 @ X22 @ X23 @ X27) @ X25)
% 0.20/0.51          | (r1_tmap_1 @ X22 @ X26 @ X27 @ X28)
% 0.20/0.51          | ((X28) != (X25))
% 0.20/0.51          | ~ (r1_tarski @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.51          | ~ (r2_hidden @ X28 @ X24)
% 0.20/0.51          | ~ (v3_pre_topc @ X24 @ X21)
% 0.20/0.51          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X22))
% 0.20/0.51          | ~ (m1_subset_1 @ X27 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X26))))
% 0.20/0.51          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X26))
% 0.20/0.51          | ~ (v1_funct_1 @ X27)
% 0.20/0.51          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.51          | (v2_struct_0 @ X23)
% 0.20/0.51          | ~ (l1_pre_topc @ X26)
% 0.20/0.51          | ~ (v2_pre_topc @ X26)
% 0.20/0.51          | (v2_struct_0 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [t85_tmap_1])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X26)
% 0.20/0.51          | ~ (v2_pre_topc @ X26)
% 0.20/0.51          | ~ (l1_pre_topc @ X26)
% 0.20/0.51          | (v2_struct_0 @ X23)
% 0.20/0.51          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.51          | ~ (v1_funct_1 @ X27)
% 0.20/0.51          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X26))
% 0.20/0.51          | ~ (m1_subset_1 @ X27 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X26))))
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 0.20/0.51          | ~ (v3_pre_topc @ X24 @ X21)
% 0.20/0.51          | ~ (r2_hidden @ X25 @ X24)
% 0.20/0.51          | ~ (r1_tarski @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.51          | (r1_tmap_1 @ X22 @ X26 @ X27 @ X25)
% 0.20/0.51          | ~ (r1_tmap_1 @ X23 @ X26 @ 
% 0.20/0.51               (k3_tmap_1 @ X21 @ X26 @ X22 @ X23 @ X27) @ X25)
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.51          | ~ (m1_pre_topc @ X23 @ X22)
% 0.20/0.51          | ~ (m1_pre_topc @ X22 @ X21)
% 0.20/0.51          | (v2_struct_0 @ X22)
% 0.20/0.51          | ~ (l1_pre_topc @ X21)
% 0.20/0.51          | ~ (v2_pre_topc @ X21)
% 0.20/0.51          | (v2_struct_0 @ X21))),
% 0.20/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.51          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.51          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.51          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.51          | ~ (v3_pre_topc @ X2 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51          | (v2_struct_0 @ X1)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['55', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.20/0.51          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.51               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X3)
% 0.20/0.51          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X3)
% 0.20/0.51          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.51          | ~ (r2_hidden @ X3 @ X2)
% 0.20/0.51          | ~ (v3_pre_topc @ X2 @ X0)
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.51          | (v2_struct_0 @ X1)
% 0.20/0.51          | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_C)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.51          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.51          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.51          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.51          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '63'])).
% 0.20/0.51  thf('65', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('66', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('68', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('69', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('71', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | (v2_struct_0 @ sk_C)
% 0.20/0.51          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | ~ (r2_hidden @ sk_F @ X0)
% 0.20/0.51          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.51          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.51          | (v2_struct_0 @ sk_D)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)],
% 0.20/0.51                ['64', '65', '66', '67', '68', '69', '70', '71'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D)
% 0.20/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.51        | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.20/0.51        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.51        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '72'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('75', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.51      inference('simplify', [status(thm)], ['74'])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf(t16_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.51                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.51                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X9 @ X10)
% 0.20/0.51          | ((X11) != (u1_struct_0 @ X9))
% 0.20/0.51          | ~ (v1_tsep_1 @ X9 @ X10)
% 0.20/0.51          | ~ (m1_pre_topc @ X9 @ X10)
% 0.20/0.51          | (v3_pre_topc @ X11 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.51          | ~ (l1_pre_topc @ X10)
% 0.20/0.51          | ~ (v2_pre_topc @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (v2_pre_topc @ X10)
% 0.20/0.51          | ~ (l1_pre_topc @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.20/0.51               (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.51          | (v3_pre_topc @ (u1_struct_0 @ X9) @ X10)
% 0.20/0.51          | ~ (v1_tsep_1 @ X9 @ X10)
% 0.20/0.51          | ~ (m1_pre_topc @ X9 @ X10))),
% 0.20/0.51      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      ((~ (m1_pre_topc @ sk_C @ sk_B)
% 0.20/0.51        | ~ (v1_tsep_1 @ sk_C @ sk_B)
% 0.20/0.51        | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B)
% 0.20/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51        | ~ (v2_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['76', '78'])).
% 0.20/0.51  thf('80', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('81', plain, ((v1_tsep_1 @ sk_C @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('83', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('84', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D)
% 0.20/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.51        | ~ (r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['73', '75', '84'])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.51        | (v2_struct_0 @ sk_D)
% 0.20/0.51        | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '85'])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.20/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.51      inference('split', [status(esa)], ['15'])).
% 0.20/0.51  thf('88', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['16', '51'])).
% 0.20/0.51  thf('89', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 0.20/0.51  thf('90', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['86', '89'])).
% 0.20/0.51  thf(fc2_struct_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      (![X8 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.20/0.51          | ~ (l1_struct_0 @ X8)
% 0.20/0.51          | (v2_struct_0 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_D)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.51  thf('93', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('95', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.51  thf(dt_l1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.51  thf('98', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('99', plain, ((l1_struct_0 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_D)
% 0.20/0.51        | (v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['92', '99'])).
% 0.20/0.51  thf('101', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | (v2_struct_0 @ sk_D)
% 0.20/0.51        | (v2_struct_0 @ sk_C)
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['100'])).
% 0.20/0.51  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.51  thf('104', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('105', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['103', '104'])).
% 0.20/0.51  thf('106', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('107', plain, ((v2_struct_0 @ sk_D)),
% 0.20/0.51      inference('clc', [status(thm)], ['105', '106'])).
% 0.20/0.51  thf('108', plain, ($false), inference('demod', [status(thm)], ['0', '107'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
