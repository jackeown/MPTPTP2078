%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dT0zEgLauS

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 768 expanded)
%              Number of leaves         :   37 ( 231 expanded)
%              Depth                    :   28
%              Number of atoms          : 2250 (29923 expanded)
%              Number of equality atoms :   31 ( 422 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( ( k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X23 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) @ X23 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( ( k2_tmap_1 @ X17 @ X15 @ X18 @ X16 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) @ X18 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','43','48','49','50','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['4'])).

thf('66',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_tmap_1,axiom,(
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
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( v1_tsep_1 @ X36 @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tmap_1 @ X36 @ X38 @ ( k2_tmap_1 @ X35 @ X38 @ X39 @ X36 ) @ X37 )
      | ( r1_tmap_1 @ X35 @ X38 @ X39 @ X40 )
      | ( X40 != X37 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X35 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('71',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ( r1_tmap_1 @ X35 @ X38 @ X39 @ X37 )
      | ~ ( r1_tmap_1 @ X36 @ X38 @ ( k2_tmap_1 @ X35 @ X38 @ X39 @ X36 ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_pre_topc @ X36 @ X35 )
      | ~ ( v1_tsep_1 @ X36 @ X35 )
      | ( v2_struct_0 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('74',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

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
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('86',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('89',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('90',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('92',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('93',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('94',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('95',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf(t19_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
               => ( ( v1_tsep_1 @ B @ C )
                  & ( m1_pre_topc @ B @ C ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_tsep_1 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ( v1_tsep_1 @ X24 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v1_tsep_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','98'])).

thf('100',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['80','81','82','83','108'])).

thf('110',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['10'])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['8'])).

thf('119',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['14','18','117','118'])).

thf('120',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['5','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
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
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('122',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ( X34 != X31 )
      | ~ ( r1_tmap_1 @ X29 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('123',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r1_tmap_1 @ X29 @ X32 @ X33 @ X31 )
      | ( r1_tmap_1 @ X30 @ X32 @ ( k2_tmap_1 @ X29 @ X32 @ X33 @ X30 ) @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('126',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('127',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['120','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','134'])).

thf('136',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('139',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('140',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('142',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('143',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['14','18','117','143'])).

thf('145',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1 ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['140','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['0','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dT0zEgLauS
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:12:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 117 iterations in 0.049s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.51  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(t87_tmap_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.51                   ( ![E:$i]:
% 0.22/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.51                         ( v1_funct_2 @
% 0.22/0.51                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                         ( m1_subset_1 @
% 0.22/0.51                           E @ 
% 0.22/0.51                           ( k1_zfmisc_1 @
% 0.22/0.51                             ( k2_zfmisc_1 @
% 0.22/0.51                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.51                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.22/0.51                           ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.51                         ( ![F:$i]:
% 0.22/0.51                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.51                             ( ![G:$i]:
% 0.22/0.51                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.51                                 ( ( ( F ) = ( G ) ) =>
% 0.22/0.51                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.22/0.51                                     ( r1_tmap_1 @
% 0.22/0.51                                       C @ A @ 
% 0.22/0.51                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51            ( l1_pre_topc @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51                ( l1_pre_topc @ B ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.51                  ( ![D:$i]:
% 0.22/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.51                      ( ![E:$i]:
% 0.22/0.51                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.51                            ( v1_funct_2 @
% 0.22/0.51                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                            ( m1_subset_1 @
% 0.22/0.51                              E @ 
% 0.22/0.51                              ( k1_zfmisc_1 @
% 0.22/0.51                                ( k2_zfmisc_1 @
% 0.22/0.51                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.51                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.22/0.51                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.51                            ( ![F:$i]:
% 0.22/0.51                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.51                                ( ![G:$i]:
% 0.22/0.51                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.51                                    ( ( ( F ) = ( G ) ) =>
% 0.22/0.51                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.22/0.51                                        ( r1_tmap_1 @
% 0.22/0.51                                          C @ A @ 
% 0.22/0.51                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.22/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('2', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.22/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.22/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('7', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.22/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('split', [status(esa)], ['10'])).
% 0.22/0.51  thf('12', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('16', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)) | 
% 0.22/0.51       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('split', [status(esa)], ['17'])).
% 0.22/0.51  thf('19', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d5_tmap_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.51                   ( ![E:$i]:
% 0.22/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.51                         ( v1_funct_2 @
% 0.22/0.51                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.51                         ( m1_subset_1 @
% 0.22/0.51                           E @ 
% 0.22/0.51                           ( k1_zfmisc_1 @
% 0.22/0.51                             ( k2_zfmisc_1 @
% 0.22/0.51                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.51                       ( ( m1_pre_topc @ D @ C ) =>
% 0.22/0.51                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.51                           ( k2_partfun1 @
% 0.22/0.51                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.22/0.51                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X19)
% 0.22/0.51          | ~ (v2_pre_topc @ X19)
% 0.22/0.51          | ~ (l1_pre_topc @ X19)
% 0.22/0.51          | ~ (m1_pre_topc @ X20 @ X21)
% 0.22/0.51          | ~ (m1_pre_topc @ X20 @ X22)
% 0.22/0.51          | ((k3_tmap_1 @ X21 @ X19 @ X22 @ X20 @ X23)
% 0.22/0.51              = (k2_partfun1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19) @ 
% 0.22/0.51                 X23 @ (u1_struct_0 @ X20)))
% 0.22/0.51          | ~ (m1_subset_1 @ X23 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))))
% 0.22/0.51          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X19))
% 0.22/0.51          | ~ (v1_funct_1 @ X23)
% 0.22/0.51          | ~ (m1_pre_topc @ X22 @ X21)
% 0.22/0.51          | ~ (l1_pre_topc @ X21)
% 0.22/0.51          | ~ (v2_pre_topc @ X21)
% 0.22/0.51          | (v2_struct_0 @ X21))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.22/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.22/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51                 sk_E @ (u1_struct_0 @ X1)))
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.51          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.22/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.51          | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '28'])).
% 0.22/0.51  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.51          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.22/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.51          | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B)
% 0.22/0.51        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.22/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.51        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '32'])).
% 0.22/0.51  thf('34', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d4_tmap_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.51                 ( m1_subset_1 @
% 0.22/0.51                   C @ 
% 0.22/0.51                   ( k1_zfmisc_1 @
% 0.22/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.51                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.22/0.51                     ( k2_partfun1 @
% 0.22/0.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.51                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X15)
% 0.22/0.51          | ~ (v2_pre_topc @ X15)
% 0.22/0.51          | ~ (l1_pre_topc @ X15)
% 0.22/0.51          | ~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.51          | ((k2_tmap_1 @ X17 @ X15 @ X18 @ X16)
% 0.22/0.51              = (k2_partfun1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ 
% 0.22/0.51                 X18 @ (u1_struct_0 @ X16)))
% 0.22/0.51          | ~ (m1_subset_1 @ X18 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 0.22/0.51          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 0.22/0.51          | ~ (v1_funct_1 @ X18)
% 0.22/0.51          | ~ (l1_pre_topc @ X17)
% 0.22/0.51          | ~ (v2_pre_topc @ X17)
% 0.22/0.51          | (v2_struct_0 @ X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.22/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X8 @ X9)
% 0.22/0.51          | (v2_pre_topc @ X8)
% 0.22/0.51          | ~ (l1_pre_topc @ X9)
% 0.22/0.51          | ~ (v2_pre_topc @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('43', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.51  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_m1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.51          | (l1_pre_topc @ X10)
% 0.22/0.51          | ~ (l1_pre_topc @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('46', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.51  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('48', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('49', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('53', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_D)
% 0.22/0.51          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.22/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51                 sk_E @ (u1_struct_0 @ X0)))
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)],
% 0.22/0.51                ['37', '43', '48', '49', '50', '51', '52'])).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.22/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51               sk_E @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.51        | (v2_struct_0 @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['34', '53'])).
% 0.22/0.51  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_D)
% 0.22/0.51        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.22/0.51            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51               sk_E @ (u1_struct_0 @ sk_C_1))))),
% 0.22/0.51      inference('clc', [status(thm)], ['54', '55'])).
% 0.22/0.51  thf('57', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)
% 0.22/0.51         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.22/0.51            (u1_struct_0 @ sk_C_1)))),
% 0.22/0.51      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.51  thf('59', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B)
% 0.22/0.51        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.22/0.51            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['33', '58', '59'])).
% 0.22/0.51  thf('61', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('62', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.22/0.51            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1)))),
% 0.22/0.51      inference('clc', [status(thm)], ['60', '61'])).
% 0.22/0.51  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.22/0.51         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))),
% 0.22/0.51      inference('clc', [status(thm)], ['62', '63'])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('split', [status(esa)], ['4'])).
% 0.22/0.51  thf('66', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['64', '67'])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t67_tmap_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                 ( m1_subset_1 @
% 0.22/0.51                   C @ 
% 0.22/0.51                   ( k1_zfmisc_1 @
% 0.22/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.22/0.51                     ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.51                   ( ![E:$i]:
% 0.22/0.51                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.51                       ( ![F:$i]:
% 0.22/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.51                           ( ( ( E ) = ( F ) ) =>
% 0.22/0.51                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.22/0.51                               ( r1_tmap_1 @
% 0.22/0.51                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('70', plain,
% 0.22/0.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X35)
% 0.22/0.51          | ~ (v2_pre_topc @ X35)
% 0.22/0.51          | ~ (l1_pre_topc @ X35)
% 0.22/0.51          | (v2_struct_0 @ X36)
% 0.22/0.51          | ~ (v1_tsep_1 @ X36 @ X35)
% 0.22/0.51          | ~ (m1_pre_topc @ X36 @ X35)
% 0.22/0.51          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.22/0.51          | ~ (r1_tmap_1 @ X36 @ X38 @ (k2_tmap_1 @ X35 @ X38 @ X39 @ X36) @ 
% 0.22/0.51               X37)
% 0.22/0.51          | (r1_tmap_1 @ X35 @ X38 @ X39 @ X40)
% 0.22/0.51          | ((X40) != (X37))
% 0.22/0.51          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X35))
% 0.22/0.51          | ~ (m1_subset_1 @ X39 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38))))
% 0.22/0.51          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38))
% 0.22/0.51          | ~ (v1_funct_1 @ X39)
% 0.22/0.51          | ~ (l1_pre_topc @ X38)
% 0.22/0.51          | ~ (v2_pre_topc @ X38)
% 0.22/0.51          | (v2_struct_0 @ X38))),
% 0.22/0.51      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X38)
% 0.22/0.51          | ~ (v2_pre_topc @ X38)
% 0.22/0.51          | ~ (l1_pre_topc @ X38)
% 0.22/0.51          | ~ (v1_funct_1 @ X39)
% 0.22/0.51          | ~ (v1_funct_2 @ X39 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38))
% 0.22/0.51          | ~ (m1_subset_1 @ X39 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X38))))
% 0.22/0.51          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.22/0.51          | (r1_tmap_1 @ X35 @ X38 @ X39 @ X37)
% 0.22/0.51          | ~ (r1_tmap_1 @ X36 @ X38 @ (k2_tmap_1 @ X35 @ X38 @ X39 @ X36) @ 
% 0.22/0.51               X37)
% 0.22/0.51          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.22/0.51          | ~ (m1_pre_topc @ X36 @ X35)
% 0.22/0.51          | ~ (v1_tsep_1 @ X36 @ X35)
% 0.22/0.51          | (v2_struct_0 @ X36)
% 0.22/0.51          | ~ (l1_pre_topc @ X35)
% 0.22/0.51          | ~ (v2_pre_topc @ X35)
% 0.22/0.51          | (v2_struct_0 @ X35))),
% 0.22/0.51      inference('simplify', [status(thm)], ['70'])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.51          | (v2_struct_0 @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.22/0.51               X1)
% 0.22/0.51          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['69', '71'])).
% 0.22/0.51  thf('73', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.51  thf('74', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('75', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('79', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_D)
% 0.22/0.51          | (v2_struct_0 @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.22/0.51               X1)
% 0.22/0.51          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)],
% 0.22/0.51                ['72', '73', '74', '75', '76', '77', '78'])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A)
% 0.22/0.51         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.51         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.22/0.51         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.22/0.51         | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.22/0.51         | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.51         | (v2_struct_0 @ sk_C_1)
% 0.22/0.51         | (v2_struct_0 @ sk_D)))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['68', '79'])).
% 0.22/0.51  thf('81', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('82', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('83', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('84', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('85', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t1_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( m1_subset_1 @
% 0.22/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('86', plain,
% 0.22/0.51      (![X27 : $i, X28 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X27 @ X28)
% 0.22/0.51          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.22/0.51          | ~ (l1_pre_topc @ X28))),
% 0.22/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.51  thf('87', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['85', '86'])).
% 0.22/0.51  thf('88', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('89', plain,
% 0.22/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['87', '88'])).
% 0.22/0.51  thf(t2_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.51  thf('90', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]:
% 0.22/0.51         ((r2_hidden @ X6 @ X7)
% 0.22/0.51          | (v1_xboole_0 @ X7)
% 0.22/0.51          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.51  thf('91', plain,
% 0.22/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.51        | (r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.51  thf(fc1_subset_1, axiom,
% 0.22/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.51  thf('92', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.51  thf('93', plain,
% 0.22/0.51      ((r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.51      inference('clc', [status(thm)], ['91', '92'])).
% 0.22/0.51  thf(d1_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.51  thf('94', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ X2)
% 0.22/0.51          | (r1_tarski @ X3 @ X1)
% 0.22/0.51          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.51  thf('95', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i]:
% 0.22/0.51         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['94'])).
% 0.22/0.51  thf('96', plain,
% 0.22/0.51      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['93', '95'])).
% 0.22/0.51  thf(t19_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.51               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.51                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('97', plain,
% 0.22/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.51         (~ (v1_tsep_1 @ X24 @ X25)
% 0.22/0.51          | ~ (m1_pre_topc @ X24 @ X25)
% 0.22/0.51          | ~ (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.22/0.51          | (v1_tsep_1 @ X24 @ X26)
% 0.22/0.51          | ~ (m1_pre_topc @ X26 @ X25)
% 0.22/0.51          | (v2_struct_0 @ X26)
% 0.22/0.51          | ~ (l1_pre_topc @ X25)
% 0.22/0.51          | ~ (v2_pre_topc @ X25)
% 0.22/0.51          | (v2_struct_0 @ X25))),
% 0.22/0.51      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.22/0.51  thf('98', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ sk_C_1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.22/0.51  thf('99', plain,
% 0.22/0.51      ((~ (v1_tsep_1 @ sk_C_1 @ sk_B)
% 0.22/0.51        | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.22/0.51        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.51        | (v2_struct_0 @ sk_D)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['84', '98'])).
% 0.22/0.51  thf('100', plain, ((v1_tsep_1 @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('101', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('103', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('104', plain,
% 0.22/0.51      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.51        | (v2_struct_0 @ sk_D)
% 0.22/0.51        | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.22/0.51  thf('105', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('106', plain, (((v2_struct_0 @ sk_B) | (v1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.22/0.51      inference('clc', [status(thm)], ['104', '105'])).
% 0.22/0.51  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('108', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 0.22/0.51      inference('clc', [status(thm)], ['106', '107'])).
% 0.22/0.51  thf('109', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A)
% 0.22/0.51         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.22/0.51         | (v2_struct_0 @ sk_C_1)
% 0.22/0.51         | (v2_struct_0 @ sk_D)))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['80', '81', '82', '83', '108'])).
% 0.22/0.51  thf('110', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['10'])).
% 0.22/0.51  thf('111', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A)))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['109', '110'])).
% 0.22/0.51  thf('112', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('113', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1)))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('clc', [status(thm)], ['111', '112'])).
% 0.22/0.51  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('115', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_C_1))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('clc', [status(thm)], ['113', '114'])).
% 0.22/0.51  thf('116', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('117', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('sup-', [status(thm)], ['115', '116'])).
% 0.22/0.51  thf('118', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))),
% 0.22/0.51      inference('split', [status(esa)], ['8'])).
% 0.22/0.51  thf('119', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['14', '18', '117', '118'])).
% 0.22/0.51  thf('120', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['5', '119'])).
% 0.22/0.51  thf('121', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t64_tmap_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                 ( m1_subset_1 @
% 0.22/0.51                   C @ 
% 0.22/0.51                   ( k1_zfmisc_1 @
% 0.22/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.52                   ( ![E:$i]:
% 0.22/0.52                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.52                       ( ![F:$i]:
% 0.22/0.52                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.52                           ( ( ( ( E ) = ( F ) ) & 
% 0.22/0.52                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.22/0.52                             ( r1_tmap_1 @
% 0.22/0.52                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('122', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X29)
% 0.22/0.52          | ~ (v2_pre_topc @ X29)
% 0.22/0.52          | ~ (l1_pre_topc @ X29)
% 0.22/0.52          | (v2_struct_0 @ X30)
% 0.22/0.52          | ~ (m1_pre_topc @ X30 @ X29)
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.22/0.52          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.22/0.52          | ((X34) != (X31))
% 0.22/0.52          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X34)
% 0.22/0.52          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X29))
% 0.22/0.52          | ~ (m1_subset_1 @ X33 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.22/0.52          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.22/0.52          | ~ (v1_funct_1 @ X33)
% 0.22/0.52          | ~ (l1_pre_topc @ X32)
% 0.22/0.52          | ~ (v2_pre_topc @ X32)
% 0.22/0.52          | (v2_struct_0 @ X32))),
% 0.22/0.52      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.22/0.52  thf('123', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X32)
% 0.22/0.52          | ~ (v2_pre_topc @ X32)
% 0.22/0.52          | ~ (l1_pre_topc @ X32)
% 0.22/0.52          | ~ (v1_funct_1 @ X33)
% 0.22/0.52          | ~ (v1_funct_2 @ X33 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))
% 0.22/0.52          | ~ (m1_subset_1 @ X33 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X32))))
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.22/0.52          | ~ (r1_tmap_1 @ X29 @ X32 @ X33 @ X31)
% 0.22/0.52          | (r1_tmap_1 @ X30 @ X32 @ (k2_tmap_1 @ X29 @ X32 @ X33 @ X30) @ X31)
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.22/0.52          | ~ (m1_pre_topc @ X30 @ X29)
% 0.22/0.52          | (v2_struct_0 @ X30)
% 0.22/0.52          | ~ (l1_pre_topc @ X29)
% 0.22/0.52          | ~ (v2_pre_topc @ X29)
% 0.22/0.52          | (v2_struct_0 @ X29))),
% 0.22/0.52      inference('simplify', [status(thm)], ['122'])).
% 0.22/0.52  thf('124', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_D)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['121', '123'])).
% 0.22/0.52  thf('125', plain, ((v2_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.52  thf('126', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('127', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('128', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('131', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.22/0.52          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['124', '125', '126', '127', '128', '129', '130'])).
% 0.22/0.52  thf('132', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.22/0.52             sk_F)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['120', '131'])).
% 0.22/0.52  thf('133', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('134', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.22/0.52             sk_F)
% 0.22/0.52          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['132', '133'])).
% 0.22/0.52  thf('135', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_C_1)
% 0.22/0.52        | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.22/0.52        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52           (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '134'])).
% 0.22/0.52  thf('136', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('137', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_D)
% 0.22/0.52        | (v2_struct_0 @ sk_C_1)
% 0.22/0.52        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52           (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['135', '136'])).
% 0.22/0.52  thf('138', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('139', plain,
% 0.22/0.52      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E)
% 0.22/0.52         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1))),
% 0.22/0.52      inference('clc', [status(thm)], ['62', '63'])).
% 0.22/0.52  thf('140', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52           (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.52      inference('demod', [status(thm)], ['138', '139'])).
% 0.22/0.52  thf('141', plain,
% 0.22/0.52      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.52         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.52      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.52  thf('142', plain,
% 0.22/0.52      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)))),
% 0.22/0.52      inference('split', [status(esa)], ['17'])).
% 0.22/0.52  thf('143', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.22/0.52       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))),
% 0.22/0.52      inference('sup-', [status(thm)], ['141', '142'])).
% 0.22/0.52  thf('144', plain,
% 0.22/0.52      (~
% 0.22/0.52       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['14', '18', '117', '143'])).
% 0.22/0.52  thf('145', plain,
% 0.22/0.52      (~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.52          (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C_1) @ sk_F)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['140', '144'])).
% 0.22/0.52  thf('146', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['137', '145'])).
% 0.22/0.52  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('148', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('clc', [status(thm)], ['146', '147'])).
% 0.22/0.52  thf('149', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('150', plain, ((v2_struct_0 @ sk_C_1)),
% 0.22/0.52      inference('clc', [status(thm)], ['148', '149'])).
% 0.22/0.52  thf('151', plain, ($false), inference('demod', [status(thm)], ['0', '150'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
