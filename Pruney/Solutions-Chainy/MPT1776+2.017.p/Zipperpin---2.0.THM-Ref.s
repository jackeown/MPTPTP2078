%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0IcUPOBiAs

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 479 expanded)
%              Number of leaves         :   25 ( 144 expanded)
%              Depth                    :   30
%              Number of atoms          : 1773 (19733 expanded)
%              Number of equality atoms :   10 ( 249 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['5'])).

thf('21',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
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
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( v1_tsep_1 @ X9 @ X7 )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ( X10 != X11 )
      | ~ ( r1_tmap_1 @ X9 @ X6 @ ( k3_tmap_1 @ X8 @ X6 @ X7 @ X9 @ X12 ) @ X11 )
      | ( r1_tmap_1 @ X7 @ X6 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( r1_tmap_1 @ X7 @ X6 @ X12 @ X11 )
      | ~ ( r1_tmap_1 @ X9 @ X6 @ ( k3_tmap_1 @ X8 @ X6 @ X7 @ X9 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ~ ( v1_tsep_1 @ X9 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
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
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( m1_pre_topc @ X3 @ X5 )
      | ( r1_tarski @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_pre_topc @ X5 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

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

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_tsep_1 @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X2 ) )
      | ( v1_tsep_1 @ X0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,(
    v1_tsep_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['32','33','34','35','36','37','38','61','62'])).

thf('64',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['11'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['9'])).

thf('75',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['15','19','73','74'])).

thf('76',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['6','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( v1_tsep_1 @ X9 @ X7 )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ( X10 != X11 )
      | ~ ( r1_tmap_1 @ X7 @ X6 @ X12 @ X10 )
      | ( r1_tmap_1 @ X9 @ X6 @ ( k3_tmap_1 @ X8 @ X6 @ X7 @ X9 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('79',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( r1_tmap_1 @ X9 @ X6 @ ( k3_tmap_1 @ X8 @ X6 @ X7 @ X9 @ X12 ) @ X11 )
      | ~ ( r1_tmap_1 @ X7 @ X6 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_pre_topc @ X9 @ X7 )
      | ~ ( v1_tsep_1 @ X9 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X1 ) )
      | ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','88'])).

thf('90',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['59','60'])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('99',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('100',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('101',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['15','19','73','101'])).

thf('103',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['98','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['0','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0IcUPOBiAs
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:01:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 57 iterations in 0.041s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.51  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
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
% 0.22/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('2', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('3', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.22/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.22/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('8', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.51        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['9'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('split', [status(esa)], ['11'])).
% 0.22/0.51  thf('13', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.22/0.51      inference('sup-', [status(thm)], ['10', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('17', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.51        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.22/0.51       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('split', [status(esa)], ['18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('split', [status(esa)], ['5'])).
% 0.22/0.51  thf('21', plain, (((sk_F) = (sk_G))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t86_tmap_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.51                   ( ![E:$i]:
% 0.22/0.51                     ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.51                         ( v1_funct_2 @
% 0.22/0.51                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.51                         ( m1_subset_1 @
% 0.22/0.51                           E @ 
% 0.22/0.51                           ( k1_zfmisc_1 @
% 0.22/0.51                             ( k2_zfmisc_1 @
% 0.22/0.51                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.51                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.22/0.51                         ( ![F:$i]:
% 0.22/0.51                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.51                             ( ![G:$i]:
% 0.22/0.51                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.51                                 ( ( ( F ) = ( G ) ) =>
% 0.22/0.51                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.22/0.51                                     ( r1_tmap_1 @
% 0.22/0.51                                       C @ B @ 
% 0.22/0.51                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X6)
% 0.22/0.51          | ~ (v2_pre_topc @ X6)
% 0.22/0.51          | ~ (l1_pre_topc @ X6)
% 0.22/0.51          | (v2_struct_0 @ X7)
% 0.22/0.51          | ~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.51          | ~ (v1_tsep_1 @ X9 @ X7)
% 0.22/0.51          | ~ (m1_pre_topc @ X9 @ X7)
% 0.22/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 0.22/0.51          | ((X10) != (X11))
% 0.22/0.51          | ~ (r1_tmap_1 @ X9 @ X6 @ (k3_tmap_1 @ X8 @ X6 @ X7 @ X9 @ X12) @ 
% 0.22/0.51               X11)
% 0.22/0.51          | (r1_tmap_1 @ X7 @ X6 @ X12 @ X10)
% 0.22/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.22/0.51          | ~ (m1_subset_1 @ X12 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.22/0.51          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.22/0.51          | ~ (v1_funct_1 @ X12)
% 0.22/0.51          | ~ (m1_pre_topc @ X9 @ X8)
% 0.22/0.51          | (v2_struct_0 @ X9)
% 0.22/0.51          | ~ (l1_pre_topc @ X8)
% 0.22/0.51          | ~ (v2_pre_topc @ X8)
% 0.22/0.51          | (v2_struct_0 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X8)
% 0.22/0.51          | ~ (v2_pre_topc @ X8)
% 0.22/0.51          | ~ (l1_pre_topc @ X8)
% 0.22/0.51          | (v2_struct_0 @ X9)
% 0.22/0.51          | ~ (m1_pre_topc @ X9 @ X8)
% 0.22/0.51          | ~ (v1_funct_1 @ X12)
% 0.22/0.51          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.22/0.51          | ~ (m1_subset_1 @ X12 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.22/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.22/0.51          | (r1_tmap_1 @ X7 @ X6 @ X12 @ X11)
% 0.22/0.51          | ~ (r1_tmap_1 @ X9 @ X6 @ (k3_tmap_1 @ X8 @ X6 @ X7 @ X9 @ X12) @ 
% 0.22/0.51               X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X7))
% 0.22/0.51          | ~ (m1_pre_topc @ X9 @ X7)
% 0.22/0.51          | ~ (v1_tsep_1 @ X9 @ X7)
% 0.22/0.51          | ~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.51          | (v2_struct_0 @ X7)
% 0.22/0.51          | ~ (l1_pre_topc @ X6)
% 0.22/0.51          | ~ (v2_pre_topc @ X6)
% 0.22/0.51          | (v2_struct_0 @ X6))),
% 0.22/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.22/0.51          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['23', '25'])).
% 0.22/0.51  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('30', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.22/0.51          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_B)
% 0.22/0.51         | ~ (v2_pre_topc @ sk_B)
% 0.22/0.51         | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51         | (v2_struct_0 @ sk_C)
% 0.22/0.51         | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.22/0.51         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.22/0.51         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.22/0.51         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.51         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.51         | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.22/0.51         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.51         | (v2_struct_0 @ sk_D)
% 0.22/0.51         | (v2_struct_0 @ sk_A)))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '31'])).
% 0.22/0.51  thf('33', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('35', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('36', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.22/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('37', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('39', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t4_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.51               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.22/0.51                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X3 @ X4)
% 0.22/0.51          | ~ (m1_pre_topc @ X3 @ X5)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X5))
% 0.22/0.51          | ~ (m1_pre_topc @ X5 @ X4)
% 0.22/0.51          | ~ (l1_pre_topc @ X4)
% 0.22/0.51          | ~ (v2_pre_topc @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v2_pre_topc @ sk_B)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.51  thf('44', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.51        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['40', '46'])).
% 0.22/0.51  thf('48', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('49', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.22/0.51  thf(t19_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.51               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.51                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (v1_tsep_1 @ X0 @ X1)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.51          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X2))
% 0.22/0.51          | (v1_tsep_1 @ X0 @ X2)
% 0.22/0.51          | ~ (m1_pre_topc @ X2 @ X1)
% 0.22/0.51          | (v2_struct_0 @ X2)
% 0.22/0.51          | ~ (l1_pre_topc @ X1)
% 0.22/0.51          | ~ (v2_pre_topc @ X1)
% 0.22/0.51          | (v2_struct_0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | (v1_tsep_1 @ sk_C @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      ((~ (v1_tsep_1 @ sk_C @ sk_B)
% 0.22/0.51        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.22/0.51        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.22/0.51        | (v2_struct_0 @ sk_D)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['39', '51'])).
% 0.22/0.51  thf('53', plain, ((v1_tsep_1 @ sk_C @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('56', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('57', plain,
% 0.22/0.51      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.22/0.51  thf('58', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('59', plain, (((v2_struct_0 @ sk_B) | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.22/0.51      inference('clc', [status(thm)], ['57', '58'])).
% 0.22/0.51  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('61', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.22/0.51      inference('clc', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('62', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_B)
% 0.22/0.51         | (v2_struct_0 @ sk_C)
% 0.22/0.51         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.22/0.51         | (v2_struct_0 @ sk_D)
% 0.22/0.51         | (v2_struct_0 @ sk_A)))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)],
% 0.22/0.51                ['32', '33', '34', '35', '36', '37', '38', '61', '62'])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['11'])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_A)
% 0.22/0.51         | (v2_struct_0 @ sk_D)
% 0.22/0.51         | (v2_struct_0 @ sk_C)
% 0.22/0.51         | (v2_struct_0 @ sk_B)))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.51  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.51  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('clc', [status(thm)], ['67', '68'])).
% 0.22/0.51  thf('70', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_C))
% 0.22/0.51         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.22/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('clc', [status(thm)], ['69', '70'])).
% 0.22/0.51  thf('72', plain, (~ (v2_struct_0 @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('73', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.22/0.51      inference('split', [status(esa)], ['9'])).
% 0.22/0.51  thf('75', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['15', '19', '73', '74'])).
% 0.22/0.51  thf('76', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['6', '75'])).
% 0.22/0.51  thf('77', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_E @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('78', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X6)
% 0.22/0.51          | ~ (v2_pre_topc @ X6)
% 0.22/0.51          | ~ (l1_pre_topc @ X6)
% 0.22/0.51          | (v2_struct_0 @ X7)
% 0.22/0.51          | ~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.51          | ~ (v1_tsep_1 @ X9 @ X7)
% 0.22/0.51          | ~ (m1_pre_topc @ X9 @ X7)
% 0.22/0.51          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 0.22/0.51          | ((X10) != (X11))
% 0.22/0.51          | ~ (r1_tmap_1 @ X7 @ X6 @ X12 @ X10)
% 0.22/0.51          | (r1_tmap_1 @ X9 @ X6 @ (k3_tmap_1 @ X8 @ X6 @ X7 @ X9 @ X12) @ X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.22/0.51          | ~ (m1_subset_1 @ X12 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.22/0.51          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.22/0.51          | ~ (v1_funct_1 @ X12)
% 0.22/0.51          | ~ (m1_pre_topc @ X9 @ X8)
% 0.22/0.51          | (v2_struct_0 @ X9)
% 0.22/0.51          | ~ (l1_pre_topc @ X8)
% 0.22/0.51          | ~ (v2_pre_topc @ X8)
% 0.22/0.51          | (v2_struct_0 @ X8))),
% 0.22/0.51      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.22/0.51  thf('79', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X8)
% 0.22/0.51          | ~ (v2_pre_topc @ X8)
% 0.22/0.51          | ~ (l1_pre_topc @ X8)
% 0.22/0.51          | (v2_struct_0 @ X9)
% 0.22/0.51          | ~ (m1_pre_topc @ X9 @ X8)
% 0.22/0.51          | ~ (v1_funct_1 @ X12)
% 0.22/0.51          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 0.22/0.51          | ~ (m1_subset_1 @ X12 @ 
% 0.22/0.51               (k1_zfmisc_1 @ 
% 0.22/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))))
% 0.22/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.22/0.51          | (r1_tmap_1 @ X9 @ X6 @ (k3_tmap_1 @ X8 @ X6 @ X7 @ X9 @ X12) @ X11)
% 0.22/0.51          | ~ (r1_tmap_1 @ X7 @ X6 @ X12 @ X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X7))
% 0.22/0.51          | ~ (m1_pre_topc @ X9 @ X7)
% 0.22/0.51          | ~ (v1_tsep_1 @ X9 @ X7)
% 0.22/0.51          | ~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.51          | (v2_struct_0 @ X7)
% 0.22/0.51          | ~ (l1_pre_topc @ X6)
% 0.22/0.51          | ~ (v2_pre_topc @ X6)
% 0.22/0.51          | (v2_struct_0 @ X6))),
% 0.22/0.51      inference('simplify', [status(thm)], ['78'])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.22/0.51          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.51             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.51          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['77', '79'])).
% 0.22/0.51  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('83', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('85', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.22/0.51          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.51             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.22/0.51          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.22/0.51  thf('86', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.51          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.22/0.51          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.51             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.22/0.51          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.51          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['76', '85'])).
% 0.22/0.51  thf('87', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('88', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((v2_struct_0 @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ X1)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ X0)
% 0.22/0.51          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X1))
% 0.22/0.51          | (r1_tmap_1 @ X1 @ sk_A @ 
% 0.22/0.51             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ sk_F)
% 0.22/0.51          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.22/0.51          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['86', '87'])).
% 0.22/0.51  thf('89', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.22/0.51          | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_C)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '88'])).
% 0.22/0.51  thf('90', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.22/0.51      inference('clc', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('91', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('92', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v2_struct_0 @ sk_A)
% 0.22/0.51          | (v2_struct_0 @ sk_D)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.22/0.51          | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51             (k3_tmap_1 @ X0 @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.22/0.51          | (v2_struct_0 @ sk_C)
% 0.22/0.51          | ~ (l1_pre_topc @ X0)
% 0.22/0.51          | ~ (v2_pre_topc @ X0)
% 0.22/0.51          | (v2_struct_0 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.22/0.51  thf('93', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B)
% 0.22/0.51        | ~ (v2_pre_topc @ sk_B)
% 0.22/0.51        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_C)
% 0.22/0.51        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.22/0.51        | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.51        | (v2_struct_0 @ sk_D)
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '92'])).
% 0.22/0.51  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('96', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('97', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B)
% 0.22/0.51        | (v2_struct_0 @ sk_C)
% 0.22/0.51        | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.22/0.51        | (v2_struct_0 @ sk_D)
% 0.22/0.51        | (v2_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 0.22/0.51  thf('98', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('99', plain,
% 0.22/0.51      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.51         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.22/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('100', plain,
% 0.22/0.51      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.22/0.51         <= (~
% 0.22/0.51             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.22/0.51      inference('split', [status(esa)], ['18'])).
% 0.22/0.51  thf('101', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.22/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.22/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.22/0.51  thf('102', plain,
% 0.22/0.51      (~
% 0.22/0.51       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['15', '19', '73', '101'])).
% 0.22/0.51  thf('103', plain,
% 0.22/0.51      (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.22/0.51          (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['98', '102'])).
% 0.22/0.51  thf('104', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_A)
% 0.22/0.51        | (v2_struct_0 @ sk_D)
% 0.22/0.51        | (v2_struct_0 @ sk_C)
% 0.22/0.51        | (v2_struct_0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['97', '103'])).
% 0.22/0.51  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('106', plain,
% 0.22/0.51      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['104', '105'])).
% 0.22/0.51  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('108', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.22/0.51      inference('clc', [status(thm)], ['106', '107'])).
% 0.22/0.51  thf('109', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('110', plain, ((v2_struct_0 @ sk_C)),
% 0.22/0.51      inference('clc', [status(thm)], ['108', '109'])).
% 0.22/0.51  thf('111', plain, ($false), inference('demod', [status(thm)], ['0', '110'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
