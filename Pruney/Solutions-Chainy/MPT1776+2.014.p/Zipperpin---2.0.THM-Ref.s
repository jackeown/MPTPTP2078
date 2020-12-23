%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YvSA0p7d7f

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 444 expanded)
%              Number of leaves         :   32 ( 136 expanded)
%              Depth                    :   32
%              Number of atoms          : 1862 (17255 expanded)
%              Number of equality atoms :   13 ( 221 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['5'])).

thf('21',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_tmap_1,axiom,(
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

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ~ ( v1_tsep_1 @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X26 ) )
      | ( X29 != X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X28 ) )
      | ( r1_tmap_1 @ X26 @ X25 @ X31 @ X30 )
      | ~ ( r1_tmap_1 @ X28 @ X25 @ ( k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X28 @ X26 )
      | ~ ( v1_tsep_1 @ X28 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('51',plain,(
    ! [X5: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('52',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('53',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','54'])).

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

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_tsep_1 @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X12 ) )
      | ( v1_tsep_1 @ X10 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v1_tsep_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_tsep_1 @ sk_C_1 @ sk_B )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','57'])).

thf('59',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_tsep_1 @ sk_C_1 @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_tsep_1 @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38','67','68'])).

thf('70',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('71',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_C_1 )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['9'])).

thf('81',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['15','19','79','80'])).

thf('82',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['6','81'])).

thf('83',plain,(
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

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X19 @ X22 )
      | ~ ( r1_tmap_1 @ X22 @ X18 @ X23 @ X21 )
      | ( X21 != X24 )
      | ( r1_tmap_1 @ X19 @ X18 @ ( k3_tmap_1 @ X20 @ X18 @ X22 @ X19 @ X23 ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t81_tmap_1])).

thf('85',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X20 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X19 ) )
      | ( r1_tmap_1 @ X19 @ X18 @ ( k3_tmap_1 @ X20 @ X18 @ X22 @ X19 @ X23 ) @ X24 )
      | ~ ( r1_tmap_1 @ X22 @ X18 @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
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
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
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
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
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
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
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
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ sk_D )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','94'])).

thf('96',plain,(
    m1_pre_topc @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('104',plain,
    ( ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('105',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('106',plain,
    ( ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['15','19','79','106'])).

thf('108',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['103','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['0','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YvSA0p7d7f
% 0.12/0.36  % Computer   : n002.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 13:56:37 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 92 iterations in 0.052s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.53  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.53  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(t87_tmap_1, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                         ( v1_funct_2 @
% 0.22/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.53                         ( m1_subset_1 @
% 0.22/0.53                           E @ 
% 0.22/0.53                           ( k1_zfmisc_1 @
% 0.22/0.53                             ( k2_zfmisc_1 @
% 0.22/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.53                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.22/0.53                           ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.53                         ( ![F:$i]:
% 0.22/0.53                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.53                             ( ![G:$i]:
% 0.22/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.53                                 ( ( ( F ) = ( G ) ) =>
% 0.22/0.53                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.22/0.53                                     ( r1_tmap_1 @
% 0.22/0.53                                       C @ A @ 
% 0.22/0.53                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.53            ( l1_pre_topc @ A ) ) =>
% 0.22/0.53          ( ![B:$i]:
% 0.22/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53                ( l1_pre_topc @ B ) ) =>
% 0.22/0.53              ( ![C:$i]:
% 0.22/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.53                  ( ![D:$i]:
% 0.22/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.53                      ( ![E:$i]:
% 0.22/0.53                        ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                            ( v1_funct_2 @
% 0.22/0.53                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.53                            ( m1_subset_1 @
% 0.22/0.53                              E @ 
% 0.22/0.53                              ( k1_zfmisc_1 @
% 0.22/0.53                                ( k2_zfmisc_1 @
% 0.22/0.53                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.53                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.22/0.53                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.53                            ( ![F:$i]:
% 0.22/0.53                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.53                                ( ![G:$i]:
% 0.22/0.53                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.53                                    ( ( ( F ) = ( G ) ) =>
% 0.22/0.53                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.22/0.53                                        ( r1_tmap_1 @
% 0.22/0.53                                          C @ A @ 
% 0.22/0.53                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.22/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('3', plain, (((sk_F) = (sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.22/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.22/0.53      inference('split', [status(esa)], ['5'])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.22/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('8', plain, (((sk_F) = (sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.22/0.53        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)))),
% 0.22/0.53      inference('split', [status(esa)], ['9'])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.22/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.53      inference('split', [status(esa)], ['11'])).
% 0.22/0.53  thf('13', plain, (((sk_F) = (sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (~
% 0.22/0.53       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)) | 
% 0.22/0.53       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)
% 0.22/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('17', plain, (((sk_F) = (sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.22/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (~
% 0.22/0.53       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)) | 
% 0.22/0.53       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.53      inference('split', [status(esa)], ['18'])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.53      inference('split', [status(esa)], ['5'])).
% 0.22/0.53  thf('21', plain, (((sk_F) = (sk_G))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.53         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.53               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_E @ 
% 0.22/0.53        (k1_zfmisc_1 @ 
% 0.22/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t86_tmap_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.53             ( l1_pre_topc @ B ) ) =>
% 0.22/0.53           ( ![C:$i]:
% 0.22/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.53               ( ![D:$i]:
% 0.22/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.53                   ( ![E:$i]:
% 0.22/0.53                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.53                         ( v1_funct_2 @
% 0.22/0.53                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.53                         ( m1_subset_1 @
% 0.22/0.53                           E @ 
% 0.22/0.53                           ( k1_zfmisc_1 @
% 0.22/0.53                             ( k2_zfmisc_1 @
% 0.22/0.53                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.53                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.53                         ( ![F:$i]:
% 0.22/0.53                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.53                             ( ![G:$i]:
% 0.22/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.53                                 ( ( ( F ) = ( G ) ) =>
% 0.22/0.53                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.22/0.53                                     ( r1_tmap_1 @
% 0.22/0.53                                       C @ B @ 
% 0.22/0.53                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X25)
% 0.22/0.53          | ~ (v2_pre_topc @ X25)
% 0.22/0.53          | ~ (l1_pre_topc @ X25)
% 0.22/0.53          | (v2_struct_0 @ X26)
% 0.22/0.53          | ~ (m1_pre_topc @ X26 @ X27)
% 0.22/0.53          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.22/0.53          | ~ (m1_pre_topc @ X28 @ X26)
% 0.22/0.53          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X26))
% 0.22/0.53          | ((X29) != (X30))
% 0.22/0.53          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.22/0.53               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.22/0.53          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X29)
% 0.22/0.53          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.22/0.53          | ~ (m1_subset_1 @ X31 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.22/0.53          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.22/0.53          | ~ (v1_funct_1 @ X31)
% 0.22/0.53          | ~ (m1_pre_topc @ X28 @ X27)
% 0.22/0.53          | (v2_struct_0 @ X28)
% 0.22/0.53          | ~ (l1_pre_topc @ X27)
% 0.22/0.53          | ~ (v2_pre_topc @ X27)
% 0.22/0.53          | (v2_struct_0 @ X27))),
% 0.22/0.53      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X30 : $i, X31 : $i]:
% 0.22/0.53         ((v2_struct_0 @ X27)
% 0.22/0.53          | ~ (v2_pre_topc @ X27)
% 0.22/0.53          | ~ (l1_pre_topc @ X27)
% 0.22/0.53          | (v2_struct_0 @ X28)
% 0.22/0.53          | ~ (m1_pre_topc @ X28 @ X27)
% 0.22/0.53          | ~ (v1_funct_1 @ X31)
% 0.22/0.53          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.22/0.53          | ~ (m1_subset_1 @ X31 @ 
% 0.22/0.53               (k1_zfmisc_1 @ 
% 0.22/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.22/0.53          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X28))
% 0.22/0.53          | (r1_tmap_1 @ X26 @ X25 @ X31 @ X30)
% 0.22/0.53          | ~ (r1_tmap_1 @ X28 @ X25 @ 
% 0.22/0.53               (k3_tmap_1 @ X27 @ X25 @ X26 @ X28 @ X31) @ X30)
% 0.22/0.53          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X26))
% 0.22/0.53          | ~ (m1_pre_topc @ X28 @ X26)
% 0.22/0.53          | ~ (v1_tsep_1 @ X28 @ X26)
% 0.22/0.53          | ~ (m1_pre_topc @ X26 @ X27)
% 0.22/0.53          | (v2_struct_0 @ X26)
% 0.22/0.53          | ~ (l1_pre_topc @ X25)
% 0.22/0.53          | ~ (v2_pre_topc @ X25)
% 0.22/0.53          | (v2_struct_0 @ X25))),
% 0.22/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_A)
% 0.22/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_D)
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.53          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.53               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.22/0.53          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.53          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.53          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.53          | (v2_struct_0 @ X1)
% 0.22/0.53          | ~ (l1_pre_topc @ X0)
% 0.22/0.53          | ~ (v2_pre_topc @ X0)
% 0.22/0.53          | (v2_struct_0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['23', '25'])).
% 0.22/0.53  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('30', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((v2_struct_0 @ sk_A)
% 0.22/0.53          | (v2_struct_0 @ sk_D)
% 0.22/0.53          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.53          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.22/0.53          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.53          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.53               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.22/0.54          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      ((((v2_struct_0 @ sk_B)
% 0.22/0.54         | ~ (v2_pre_topc @ sk_B)
% 0.22/0.54         | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54         | (v2_struct_0 @ sk_C_1)
% 0.22/0.54         | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.22/0.54         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))
% 0.22/0.54         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.22/0.54         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.54         | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.22/0.54         | ~ (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.54         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.54         | (v2_struct_0 @ sk_D)
% 0.22/0.54         | (v2_struct_0 @ sk_A)))
% 0.22/0.54         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '31'])).
% 0.22/0.54  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('35', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('36', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.54  thf('37', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('38', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('40', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t1_tsep_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.54           ( m1_subset_1 @
% 0.22/0.54             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X13 @ X14)
% 0.22/0.54          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.22/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.54          | ~ (l1_pre_topc @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.54        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf('43', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(dt_m1_pre_topc, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( l1_pre_topc @ A ) =>
% 0.22/0.54       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.54  thf('45', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.54  thf('46', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('47', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.54      inference('demod', [status(thm)], ['42', '47'])).
% 0.22/0.54  thf(t2_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]:
% 0.22/0.54         ((r2_hidden @ X6 @ X7)
% 0.22/0.54          | (v1_xboole_0 @ X7)
% 0.22/0.54          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.22/0.54        | (r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.54  thf(fc1_subset_1, axiom,
% 0.22/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.54  thf('51', plain, (![X5 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      ((r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.22/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.22/0.54      inference('clc', [status(thm)], ['50', '51'])).
% 0.22/0.54  thf(d1_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X3 @ X2)
% 0.22/0.54          | (r1_tarski @ X3 @ X1)
% 0.22/0.54          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('sup-', [status(thm)], ['52', '54'])).
% 0.22/0.54  thf(t19_tsep_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.54               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.54                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.54         (~ (v1_tsep_1 @ X10 @ X11)
% 0.22/0.54          | ~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.54          | ~ (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X12))
% 0.22/0.54          | (v1_tsep_1 @ X10 @ X12)
% 0.22/0.54          | ~ (m1_pre_topc @ X12 @ X11)
% 0.22/0.54          | (v2_struct_0 @ X12)
% 0.22/0.54          | ~ (l1_pre_topc @ X11)
% 0.22/0.54          | ~ (v2_pre_topc @ X11)
% 0.22/0.54          | (v2_struct_0 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.54          | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.22/0.54          | ~ (v1_tsep_1 @ sk_C_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      ((~ (v1_tsep_1 @ sk_C_1 @ sk_B)
% 0.22/0.54        | ~ (m1_pre_topc @ sk_C_1 @ sk_B)
% 0.22/0.54        | (v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54        | ~ (v2_pre_topc @ sk_B)
% 0.22/0.54        | (v2_struct_0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['39', '57'])).
% 0.22/0.54  thf('59', plain, ((v1_tsep_1 @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('60', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('62', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (((v1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | (v2_struct_0 @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.22/0.54  thf('64', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('65', plain, (((v2_struct_0 @ sk_B) | (v1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.22/0.54      inference('clc', [status(thm)], ['63', '64'])).
% 0.22/0.54  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('67', plain, ((v1_tsep_1 @ sk_C_1 @ sk_D)),
% 0.22/0.54      inference('clc', [status(thm)], ['65', '66'])).
% 0.22/0.54  thf('68', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('69', plain,
% 0.22/0.54      ((((v2_struct_0 @ sk_B)
% 0.22/0.54         | (v2_struct_0 @ sk_C_1)
% 0.22/0.54         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.22/0.54         | (v2_struct_0 @ sk_D)
% 0.22/0.54         | (v2_struct_0 @ sk_A)))
% 0.22/0.54         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.54      inference('demod', [status(thm)],
% 0.22/0.54                ['32', '33', '34', '35', '36', '37', '38', '67', '68'])).
% 0.22/0.54  thf('70', plain,
% 0.22/0.54      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.22/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.22/0.54      inference('split', [status(esa)], ['11'])).
% 0.22/0.54  thf('71', plain,
% 0.22/0.54      ((((v2_struct_0 @ sk_A)
% 0.22/0.54         | (v2_struct_0 @ sk_D)
% 0.22/0.54         | (v2_struct_0 @ sk_C_1)
% 0.22/0.54         | (v2_struct_0 @ sk_B)))
% 0.22/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.54  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('73', plain,
% 0.22/0.54      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D)))
% 0.22/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.54  thf('74', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('75', plain,
% 0.22/0.54      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1)))
% 0.22/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.54      inference('clc', [status(thm)], ['73', '74'])).
% 0.22/0.54  thf('76', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('77', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_C_1))
% 0.22/0.54         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.54      inference('clc', [status(thm)], ['75', '76'])).
% 0.22/0.54  thf('78', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('79', plain,
% 0.22/0.54      (~
% 0.22/0.54       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.22/0.54       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.22/0.54  thf('80', plain,
% 0.22/0.54      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.22/0.54       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))),
% 0.22/0.54      inference('split', [status(esa)], ['9'])).
% 0.22/0.54  thf('81', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['15', '19', '79', '80'])).
% 0.22/0.54  thf('82', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['6', '81'])).
% 0.22/0.54  thf('83', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_E @ 
% 0.22/0.54        (k1_zfmisc_1 @ 
% 0.22/0.54         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t81_tmap_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.54             ( l1_pre_topc @ B ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.54               ( ![D:$i]:
% 0.22/0.54                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.54                   ( ![E:$i]:
% 0.22/0.54                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.54                         ( v1_funct_2 @
% 0.22/0.54                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.54                         ( m1_subset_1 @
% 0.22/0.54                           E @ 
% 0.22/0.54                           ( k1_zfmisc_1 @
% 0.22/0.54                             ( k2_zfmisc_1 @
% 0.22/0.54                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.54                       ( ![F:$i]:
% 0.22/0.54                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.54                           ( ![G:$i]:
% 0.22/0.54                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.54                               ( ( ( ( F ) = ( G ) ) & 
% 0.22/0.54                                   ( m1_pre_topc @ D @ C ) & 
% 0.22/0.54                                   ( r1_tmap_1 @ C @ B @ E @ F ) ) =>
% 0.22/0.54                                 ( r1_tmap_1 @
% 0.22/0.54                                   D @ B @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.22/0.54                                   G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf('84', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X18)
% 0.22/0.54          | ~ (v2_pre_topc @ X18)
% 0.22/0.54          | ~ (l1_pre_topc @ X18)
% 0.22/0.54          | (v2_struct_0 @ X19)
% 0.22/0.54          | ~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.54          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.22/0.54          | ~ (m1_pre_topc @ X19 @ X22)
% 0.22/0.54          | ~ (r1_tmap_1 @ X22 @ X18 @ X23 @ X21)
% 0.22/0.54          | ((X21) != (X24))
% 0.22/0.54          | (r1_tmap_1 @ X19 @ X18 @ 
% 0.22/0.54             (k3_tmap_1 @ X20 @ X18 @ X22 @ X19 @ X23) @ X24)
% 0.22/0.54          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X19))
% 0.22/0.54          | ~ (m1_subset_1 @ X23 @ 
% 0.22/0.54               (k1_zfmisc_1 @ 
% 0.22/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X18))))
% 0.22/0.54          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X18))
% 0.22/0.54          | ~ (v1_funct_1 @ X23)
% 0.22/0.54          | ~ (m1_pre_topc @ X22 @ X20)
% 0.22/0.54          | (v2_struct_0 @ X22)
% 0.22/0.54          | ~ (l1_pre_topc @ X20)
% 0.22/0.54          | ~ (v2_pre_topc @ X20)
% 0.22/0.54          | (v2_struct_0 @ X20))),
% 0.22/0.54      inference('cnf', [status(esa)], [t81_tmap_1])).
% 0.22/0.54  thf('85', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X20)
% 0.22/0.54          | ~ (v2_pre_topc @ X20)
% 0.22/0.54          | ~ (l1_pre_topc @ X20)
% 0.22/0.54          | (v2_struct_0 @ X22)
% 0.22/0.54          | ~ (m1_pre_topc @ X22 @ X20)
% 0.22/0.54          | ~ (v1_funct_1 @ X23)
% 0.22/0.54          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X18))
% 0.22/0.54          | ~ (m1_subset_1 @ X23 @ 
% 0.22/0.54               (k1_zfmisc_1 @ 
% 0.22/0.54                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X18))))
% 0.22/0.54          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X19))
% 0.22/0.54          | (r1_tmap_1 @ X19 @ X18 @ 
% 0.22/0.54             (k3_tmap_1 @ X20 @ X18 @ X22 @ X19 @ X23) @ X24)
% 0.22/0.54          | ~ (r1_tmap_1 @ X22 @ X18 @ X23 @ X24)
% 0.22/0.54          | ~ (m1_pre_topc @ X19 @ X22)
% 0.22/0.54          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 0.22/0.54          | ~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.54          | (v2_struct_0 @ X19)
% 0.22/0.54          | ~ (l1_pre_topc @ X18)
% 0.22/0.54          | ~ (v2_pre_topc @ X18)
% 0.22/0.54          | (v2_struct_0 @ X18))),
% 0.22/0.54      inference('simplify', [status(thm)], ['84'])).
% 0.22/0.54  thf('86', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_A)
% 0.22/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.54          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.22/0.54          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.22/0.54             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.54          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (l1_pre_topc @ X1)
% 0.22/0.54          | ~ (v2_pre_topc @ X1)
% 0.22/0.54          | (v2_struct_0 @ X1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['83', '85'])).
% 0.22/0.54  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('89', plain,
% 0.22/0.54      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('90', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('91', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ X0)
% 0.22/0.54          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.54          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.22/0.54          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.22/0.54          | (r1_tmap_1 @ X0 @ sk_A @ 
% 0.22/0.54             (k3_tmap_1 @ X1 @ sk_A @ sk_D @ X0 @ sk_E) @ X2)
% 0.22/0.54          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (l1_pre_topc @ X1)
% 0.22/0.54          | ~ (v2_pre_topc @ X1)
% 0.22/0.54          | (v2_struct_0 @ X1))),
% 0.22/0.54      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 0.22/0.54  thf('92', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.22/0.54          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.54             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['82', '91'])).
% 0.22/0.54  thf('93', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('94', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((v2_struct_0 @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.54          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.22/0.54          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.54             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.54          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.54          | (v2_struct_0 @ X1)
% 0.22/0.54          | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['92', '93'])).
% 0.22/0.54  thf('95', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_C_1)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_C_1 @ sk_D)
% 0.22/0.54          | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '94'])).
% 0.22/0.54  thf('96', plain, ((m1_pre_topc @ sk_C_1 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('97', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((v2_struct_0 @ sk_A)
% 0.22/0.54          | (v2_struct_0 @ sk_C_1)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.22/0.54          | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.22/0.54          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.54          | (v2_struct_0 @ sk_D)
% 0.22/0.54          | ~ (l1_pre_topc @ X0)
% 0.22/0.54          | ~ (v2_pre_topc @ X0)
% 0.22/0.54          | (v2_struct_0 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['95', '96'])).
% 0.22/0.54  thf('98', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B)
% 0.22/0.54        | ~ (v2_pre_topc @ sk_B)
% 0.22/0.54        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.54        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.22/0.54        | (v2_struct_0 @ sk_C_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '97'])).
% 0.22/0.54  thf('99', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('101', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('102', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)
% 0.22/0.54        | (v2_struct_0 @ sk_C_1)
% 0.22/0.54        | (v2_struct_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.22/0.54  thf('103', plain,
% 0.22/0.54      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.54         <= (~
% 0.22/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.54      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('104', plain,
% 0.22/0.54      (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.54         <= (((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)))),
% 0.22/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.54  thf('105', plain,
% 0.22/0.54      ((~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))
% 0.22/0.54         <= (~
% 0.22/0.54             ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)))),
% 0.22/0.54      inference('split', [status(esa)], ['18'])).
% 0.22/0.54  thf('106', plain,
% 0.22/0.54      (~
% 0.22/0.54       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G)) | 
% 0.22/0.54       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F))),
% 0.22/0.54      inference('sup-', [status(thm)], ['104', '105'])).
% 0.22/0.54  thf('107', plain,
% 0.22/0.54      (~
% 0.22/0.54       ((r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_G))),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['15', '19', '79', '106'])).
% 0.22/0.54  thf('108', plain,
% 0.22/0.54      (~ (r1_tmap_1 @ sk_C_1 @ sk_A @ 
% 0.22/0.54          (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 @ sk_E) @ sk_F)),
% 0.22/0.54      inference('simpl_trail', [status(thm)], ['103', '107'])).
% 0.22/0.54  thf('109', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_A)
% 0.22/0.54        | (v2_struct_0 @ sk_C_1)
% 0.22/0.54        | (v2_struct_0 @ sk_D)
% 0.22/0.54        | (v2_struct_0 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['102', '108'])).
% 0.22/0.54  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('111', plain,
% 0.22/0.54      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['109', '110'])).
% 0.22/0.54  thf('112', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('113', plain, (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_D))),
% 0.22/0.54      inference('clc', [status(thm)], ['111', '112'])).
% 0.22/0.54  thf('114', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('115', plain, ((v2_struct_0 @ sk_D)),
% 0.22/0.54      inference('clc', [status(thm)], ['113', '114'])).
% 0.22/0.54  thf('116', plain, ($false), inference('demod', [status(thm)], ['0', '115'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
