%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YMmwTDY3na

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:11 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  177 (1009 expanded)
%              Number of leaves         :   34 ( 291 expanded)
%              Depth                    :   19
%              Number of atoms          : 2057 (52740 expanded)
%              Number of equality atoms :   59 ( 660 expanded)
%              Maximal formula depth    :   25 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t80_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ! [G: $i] :
                              ( ( ( v1_funct_1 @ G )
                                & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( ( D = A )
                                  & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                               => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                               => ( ( ( D = A )
                                    & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                                 => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                  <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_tmap_1])).

thf('0',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( k2_tmap_1 @ X15 @ X13 @ X16 @ X14 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) @ X16 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_partfun1 @ X1 @ X2 @ X0 @ X3 )
        = ( k7_relat_1 @ X0 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14','17','18','21','26','27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','34'])).

thf('36',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('52',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['43'])).

thf('54',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('55',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('56',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('60',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( ( k3_tmap_1 @ X19 @ X17 @ X20 @ X18 @ X21 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X17 ) @ X21 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X21 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('74',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('89',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('90',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('93',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( X7 = X11 )
      | ~ ( r1_funct_2 @ X8 @ X9 @ X12 @ X10 @ X7 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('101',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_funct_2 @ sk_G @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('104',plain,(
    v1_funct_2 @ sk_G @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['88','89'])).

thf('109',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['98','99','104','109'])).

thf('111',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( sk_E = sk_G ) ),
    inference('sup+',[status(thm)],['82','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('115',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['112','115'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('117',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('118',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['113','114'])).

thf('120',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('124',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['81','126'])).

thf('128',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['58','127'])).

thf('129',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('130',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['43'])).

thf('131',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['45','52','53','128','131'])).

thf('133',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['35','132'])).

thf('134',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('135',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['120','121'])).

thf('136',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('137',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['36'])).

thf('139',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['45','52','53','128','131','138'])).

thf('140',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['137','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['133','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YMmwTDY3na
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 355 iterations in 0.144s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.60  thf(sk_G_type, type, sk_G: $i).
% 0.41/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.60  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.41/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.60  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.60  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(t80_tmap_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.41/0.60                   ( ![E:$i]:
% 0.41/0.60                     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.60                         ( v1_funct_2 @
% 0.41/0.60                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                         ( m1_subset_1 @
% 0.41/0.60                           E @ 
% 0.41/0.60                           ( k1_zfmisc_1 @
% 0.41/0.60                             ( k2_zfmisc_1 @
% 0.41/0.60                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                       ( ![F:$i]:
% 0.41/0.60                         ( ( ( v1_funct_1 @ F ) & 
% 0.41/0.60                             ( v1_funct_2 @
% 0.41/0.60                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                             ( m1_subset_1 @
% 0.41/0.60                               F @ 
% 0.41/0.60                               ( k1_zfmisc_1 @
% 0.41/0.60                                 ( k2_zfmisc_1 @
% 0.41/0.60                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                           ( ![G:$i]:
% 0.41/0.60                             ( ( ( v1_funct_1 @ G ) & 
% 0.41/0.60                                 ( v1_funct_2 @
% 0.41/0.60                                   G @ ( u1_struct_0 @ D ) @ 
% 0.41/0.60                                   ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                                 ( m1_subset_1 @
% 0.41/0.60                                   G @ 
% 0.41/0.60                                   ( k1_zfmisc_1 @
% 0.41/0.60                                     ( k2_zfmisc_1 @
% 0.41/0.60                                       ( u1_struct_0 @ D ) @ 
% 0.41/0.60                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                               ( ( ( ( D ) = ( A ) ) & 
% 0.41/0.60                                   ( r1_funct_2 @
% 0.41/0.60                                     ( u1_struct_0 @ A ) @ 
% 0.41/0.60                                     ( u1_struct_0 @ B ) @ 
% 0.41/0.60                                     ( u1_struct_0 @ D ) @ 
% 0.41/0.60                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.41/0.60                                 ( ( r2_funct_2 @
% 0.41/0.60                                     ( u1_struct_0 @ C ) @ 
% 0.41/0.60                                     ( u1_struct_0 @ B ) @ 
% 0.41/0.60                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.41/0.60                                   ( r2_funct_2 @
% 0.41/0.60                                     ( u1_struct_0 @ C ) @ 
% 0.41/0.60                                     ( u1_struct_0 @ B ) @ 
% 0.41/0.60                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.60            ( l1_pre_topc @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60                ( l1_pre_topc @ B ) ) =>
% 0.41/0.60              ( ![C:$i]:
% 0.41/0.60                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.60                  ( ![D:$i]:
% 0.41/0.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.41/0.60                      ( ![E:$i]:
% 0.41/0.60                        ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.60                            ( v1_funct_2 @
% 0.41/0.60                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                            ( m1_subset_1 @
% 0.41/0.60                              E @ 
% 0.41/0.60                              ( k1_zfmisc_1 @
% 0.41/0.60                                ( k2_zfmisc_1 @
% 0.41/0.60                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                          ( ![F:$i]:
% 0.41/0.60                            ( ( ( v1_funct_1 @ F ) & 
% 0.41/0.60                                ( v1_funct_2 @
% 0.41/0.60                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                                ( m1_subset_1 @
% 0.41/0.60                                  F @ 
% 0.41/0.60                                  ( k1_zfmisc_1 @
% 0.41/0.60                                    ( k2_zfmisc_1 @
% 0.41/0.60                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                              ( ![G:$i]:
% 0.41/0.60                                ( ( ( v1_funct_1 @ G ) & 
% 0.41/0.60                                    ( v1_funct_2 @
% 0.41/0.60                                      G @ ( u1_struct_0 @ D ) @ 
% 0.41/0.60                                      ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                                    ( m1_subset_1 @
% 0.41/0.60                                      G @ 
% 0.41/0.60                                      ( k1_zfmisc_1 @
% 0.41/0.60                                        ( k2_zfmisc_1 @
% 0.41/0.60                                          ( u1_struct_0 @ D ) @ 
% 0.41/0.60                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60                                  ( ( ( ( D ) = ( A ) ) & 
% 0.41/0.60                                      ( r1_funct_2 @
% 0.41/0.60                                        ( u1_struct_0 @ A ) @ 
% 0.41/0.60                                        ( u1_struct_0 @ B ) @ 
% 0.41/0.60                                        ( u1_struct_0 @ D ) @ 
% 0.41/0.60                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 0.41/0.60                                    ( ( r2_funct_2 @
% 0.41/0.60                                        ( u1_struct_0 @ C ) @ 
% 0.41/0.60                                        ( u1_struct_0 @ B ) @ 
% 0.41/0.60                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 0.41/0.60                                      ( r2_funct_2 @
% 0.41/0.60                                        ( u1_struct_0 @ C ) @ 
% 0.41/0.60                                        ( u1_struct_0 @ B ) @ 
% 0.41/0.60                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.41/0.60        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.41/0.60         <= (~
% 0.41/0.60             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.60      inference('split', [status(esa)], ['0'])).
% 0.41/0.60  thf('2', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.41/0.60         <= (~
% 0.41/0.60             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('5', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_E @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('8', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_E @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf(d4_tmap_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.60             ( l1_pre_topc @ B ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.60                 ( m1_subset_1 @
% 0.41/0.60                   C @ 
% 0.41/0.60                   ( k1_zfmisc_1 @
% 0.41/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.60               ( ![D:$i]:
% 0.41/0.60                 ( ( m1_pre_topc @ D @ A ) =>
% 0.41/0.60                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.41/0.60                     ( k2_partfun1 @
% 0.41/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.41/0.60                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X13)
% 0.41/0.60          | ~ (v2_pre_topc @ X13)
% 0.41/0.60          | ~ (l1_pre_topc @ X13)
% 0.41/0.60          | ~ (m1_pre_topc @ X14 @ X15)
% 0.41/0.60          | ((k2_tmap_1 @ X15 @ X13 @ X16 @ X14)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13) @ 
% 0.41/0.60                 X16 @ (u1_struct_0 @ X14)))
% 0.41/0.60          | ~ (m1_subset_1 @ X16 @ 
% 0.41/0.60               (k1_zfmisc_1 @ 
% 0.41/0.60                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))))
% 0.41/0.60          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X13))
% 0.41/0.60          | ~ (v1_funct_1 @ X16)
% 0.41/0.60          | ~ (l1_pre_topc @ X15)
% 0.41/0.60          | ~ (v2_pre_topc @ X15)
% 0.41/0.60          | (v2_struct_0 @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_D)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_D)
% 0.41/0.60          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.60          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.60          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.41/0.60              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60                 sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.60          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('13', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('14', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.60  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('16', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.41/0.60  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('20', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      ((m1_subset_1 @ sk_E @ 
% 0.41/0.60        (k1_zfmisc_1 @ 
% 0.41/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf(redefinition_k2_partfun1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.60       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.41/0.60          | ~ (v1_funct_1 @ X0)
% 0.41/0.60          | ((k2_partfun1 @ X1 @ X2 @ X0 @ X3) = (k7_relat_1 @ X0 @ X3)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.41/0.60            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.41/0.60          | ~ (v1_funct_1 @ sk_E))),
% 0.41/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.60  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.41/0.60           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.60  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('28', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ sk_D)
% 0.41/0.60          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.41/0.60              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.60          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.60          | (v2_struct_0 @ sk_B))),
% 0.41/0.60      inference('demod', [status(thm)],
% 0.41/0.60                ['11', '14', '17', '18', '21', '26', '27', '28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B)
% 0.41/0.60        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.41/0.60            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.41/0.60        | (v2_struct_0 @ sk_D))),
% 0.41/0.60      inference('sup-', [status(thm)], ['6', '29'])).
% 0.41/0.60  thf('31', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_D)
% 0.41/0.60        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.41/0.60            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.41/0.60      inference('clc', [status(thm)], ['30', '31'])).
% 0.41/0.60  thf('33', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.41/0.60         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.41/0.60      inference('clc', [status(thm)], ['32', '33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 0.41/0.60         <= (~
% 0.41/0.60             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.60      inference('demod', [status(thm)], ['3', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.41/0.60        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.41/0.60         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.60      inference('split', [status(esa)], ['36'])).
% 0.41/0.60  thf('38', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.41/0.60         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.41/0.60        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('41', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('42', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.41/0.60        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.60      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.41/0.60         <= (~
% 0.41/0.60             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.60      inference('split', [status(esa)], ['43'])).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 0.41/0.60       ~
% 0.41/0.60       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '44'])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.41/0.60        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('47', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('48', plain, (((sk_D) = (sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)
% 0.41/0.60        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.60      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.41/0.60         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.60      inference('split', [status(esa)], ['49'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.41/0.60         <= (~
% 0.41/0.60             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.60      inference('demod', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.61      (~
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.41/0.61      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (~
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 0.41/0.61       ~
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.61      inference('split', [status(esa)], ['43'])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.41/0.61         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.41/0.61      inference('clc', [status(thm)], ['32', '33'])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.41/0.61         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.61      inference('split', [status(esa)], ['36'])).
% 0.41/0.61  thf('56', plain, (((sk_D) = (sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.41/0.61         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.61      inference('demod', [status(thm)], ['55', '56'])).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 0.41/0.61         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['54', '57'])).
% 0.41/0.61  thf('59', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('60', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('61', plain, (((sk_D) = (sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('62', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['60', '61'])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_E @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf(d5_tmap_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.61             ( l1_pre_topc @ B ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.61               ( ![D:$i]:
% 0.41/0.61                 ( ( m1_pre_topc @ D @ A ) =>
% 0.41/0.61                   ( ![E:$i]:
% 0.41/0.61                     ( ( ( v1_funct_1 @ E ) & 
% 0.41/0.61                         ( v1_funct_2 @
% 0.41/0.61                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.61                         ( m1_subset_1 @
% 0.41/0.61                           E @ 
% 0.41/0.61                           ( k1_zfmisc_1 @
% 0.41/0.61                             ( k2_zfmisc_1 @
% 0.41/0.61                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.61                       ( ( m1_pre_topc @ D @ C ) =>
% 0.41/0.61                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.41/0.61                           ( k2_partfun1 @
% 0.41/0.61                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.41/0.61                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X17)
% 0.41/0.61          | ~ (v2_pre_topc @ X17)
% 0.41/0.61          | ~ (l1_pre_topc @ X17)
% 0.41/0.61          | ~ (m1_pre_topc @ X18 @ X19)
% 0.41/0.61          | ~ (m1_pre_topc @ X18 @ X20)
% 0.41/0.61          | ((k3_tmap_1 @ X19 @ X17 @ X20 @ X18 @ X21)
% 0.41/0.61              = (k2_partfun1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X17) @ 
% 0.41/0.61                 X21 @ (u1_struct_0 @ X18)))
% 0.41/0.61          | ~ (m1_subset_1 @ X21 @ 
% 0.41/0.61               (k1_zfmisc_1 @ 
% 0.41/0.61                (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X17))))
% 0.41/0.61          | ~ (v1_funct_2 @ X21 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X17))
% 0.41/0.61          | ~ (v1_funct_1 @ X21)
% 0.41/0.61          | ~ (m1_pre_topc @ X20 @ X19)
% 0.41/0.61          | ~ (l1_pre_topc @ X19)
% 0.41/0.61          | ~ (v2_pre_topc @ X19)
% 0.41/0.61          | (v2_struct_0 @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.41/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.41/0.61              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61                 sk_E @ (u1_struct_0 @ X1)))
% 0.41/0.61          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.61          | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.41/0.61  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.61  thf('68', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.41/0.61           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.61  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((v2_struct_0 @ X0)
% 0.41/0.61          | ~ (v2_pre_topc @ X0)
% 0.41/0.61          | ~ (l1_pre_topc @ X0)
% 0.41/0.61          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.41/0.61          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.41/0.61              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.41/0.61          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ X1 @ X0)
% 0.41/0.61          | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['65', '66', '67', '68', '69', '70'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.61          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.41/0.61              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.61          | ~ (l1_pre_topc @ sk_D)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_D)
% 0.41/0.61          | (v2_struct_0 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['62', '71'])).
% 0.41/0.61  thf('73', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.41/0.61  thf('74', plain, ((v2_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.41/0.61  thf('75', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_B)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.61          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.41/0.61              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.61          | (v2_struct_0 @ sk_D))),
% 0.41/0.61      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_D)
% 0.41/0.61          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)
% 0.41/0.61              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.41/0.61          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.41/0.61          | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('simplify', [status(thm)], ['75'])).
% 0.41/0.61  thf('77', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_B)
% 0.41/0.61        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.41/0.61            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.41/0.61        | (v2_struct_0 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['59', '76'])).
% 0.41/0.61  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_D)
% 0.41/0.61        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.41/0.61            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.41/0.61      inference('clc', [status(thm)], ['77', '78'])).
% 0.41/0.61  thf('80', plain, (~ (v2_struct_0 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.41/0.61         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.41/0.61      inference('clc', [status(thm)], ['79', '80'])).
% 0.41/0.61  thf(d3_struct_0, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.61  thf('82', plain,
% 0.41/0.61      (![X4 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('83', plain,
% 0.41/0.61      (![X4 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('84', plain,
% 0.41/0.61      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('85', plain, (((sk_D) = (sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('86', plain,
% 0.41/0.61      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.41/0.61      inference('demod', [status(thm)], ['84', '85'])).
% 0.41/0.61  thf('87', plain,
% 0.41/0.61      (((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)
% 0.41/0.61        | ~ (l1_struct_0 @ sk_D))),
% 0.41/0.61      inference('sup+', [status(thm)], ['83', '86'])).
% 0.41/0.61  thf('88', plain, ((l1_pre_topc @ sk_D)),
% 0.41/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.41/0.61  thf(dt_l1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.61  thf('89', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('90', plain, ((l1_struct_0 @ sk_D)),
% 0.41/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.41/0.61  thf('91', plain,
% 0.41/0.61      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61        (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 0.41/0.61      inference('demod', [status(thm)], ['87', '90'])).
% 0.41/0.61  thf('92', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_E @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf(redefinition_r1_funct_2, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.61     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.41/0.61         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.41/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.61         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.41/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.41/0.61       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.41/0.61  thf('93', plain,
% 0.41/0.61      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.41/0.61          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 0.41/0.61          | ~ (v1_funct_1 @ X7)
% 0.41/0.61          | (v1_xboole_0 @ X10)
% 0.41/0.61          | (v1_xboole_0 @ X9)
% 0.41/0.61          | ~ (v1_funct_1 @ X11)
% 0.41/0.61          | ~ (v1_funct_2 @ X11 @ X12 @ X10)
% 0.41/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 0.41/0.61          | ((X7) = (X11))
% 0.41/0.61          | ~ (r1_funct_2 @ X8 @ X9 @ X12 @ X10 @ X7 @ X11))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.41/0.61  thf('94', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.41/0.61             X1 @ sk_E @ X0)
% 0.41/0.61          | ((sk_E) = (X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.41/0.61          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.41/0.61          | ~ (v1_funct_1 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | (v1_xboole_0 @ X1)
% 0.41/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.41/0.61          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['92', '93'])).
% 0.41/0.61  thf('95', plain, ((v1_funct_1 @ sk_E)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('96', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.61  thf('97', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 0.41/0.61             X1 @ sk_E @ X0)
% 0.41/0.61          | ((sk_E) = (X0))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.41/0.61          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.41/0.61          | ~ (v1_funct_1 @ X0)
% 0.41/0.61          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61          | (v1_xboole_0 @ X1))),
% 0.41/0.61      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.41/0.61  thf('98', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | ~ (v1_funct_1 @ sk_G)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_G @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | ~ (m1_subset_1 @ sk_G @ 
% 0.41/0.61             (k1_zfmisc_1 @ 
% 0.41/0.61              (k2_zfmisc_1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.41/0.61        | ((sk_E) = (sk_G)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['91', '97'])).
% 0.41/0.61  thf('99', plain, ((v1_funct_1 @ sk_G)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('100', plain,
% 0.41/0.61      (![X4 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('101', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('102', plain,
% 0.41/0.61      (((v1_funct_2 @ sk_G @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_D))),
% 0.41/0.61      inference('sup+', [status(thm)], ['100', '101'])).
% 0.41/0.61  thf('103', plain, ((l1_struct_0 @ sk_D)),
% 0.41/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.41/0.61  thf('104', plain,
% 0.41/0.61      ((v1_funct_2 @ sk_G @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['102', '103'])).
% 0.41/0.61  thf('105', plain,
% 0.41/0.61      (![X4 : $i]:
% 0.41/0.61         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.61  thf('106', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_G @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('107', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_G @ 
% 0.41/0.61         (k1_zfmisc_1 @ 
% 0.41/0.61          (k2_zfmisc_1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_D))),
% 0.41/0.61      inference('sup+', [status(thm)], ['105', '106'])).
% 0.41/0.61  thf('108', plain, ((l1_struct_0 @ sk_D)),
% 0.41/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.41/0.61  thf('109', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_G @ 
% 0.41/0.61        (k1_zfmisc_1 @ 
% 0.41/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.61      inference('demod', [status(thm)], ['107', '108'])).
% 0.41/0.61  thf('110', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.41/0.61        | ((sk_E) = (sk_G)))),
% 0.41/0.61      inference('demod', [status(thm)], ['98', '99', '104', '109'])).
% 0.41/0.61  thf('111', plain,
% 0.41/0.61      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['110'])).
% 0.41/0.61  thf('112', plain,
% 0.41/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.41/0.61        | ~ (l1_struct_0 @ sk_B)
% 0.41/0.61        | ((sk_E) = (sk_G)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['82', '111'])).
% 0.41/0.61  thf('113', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('114', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('115', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.61      inference('sup-', [status(thm)], ['113', '114'])).
% 0.41/0.61  thf('116', plain,
% 0.41/0.61      (((v1_xboole_0 @ (k2_struct_0 @ sk_B)) | ((sk_E) = (sk_G)))),
% 0.41/0.61      inference('demod', [status(thm)], ['112', '115'])).
% 0.41/0.61  thf(fc5_struct_0, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.61       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.41/0.61  thf('117', plain,
% 0.41/0.61      (![X6 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ (k2_struct_0 @ X6))
% 0.41/0.61          | ~ (l1_struct_0 @ X6)
% 0.41/0.61          | (v2_struct_0 @ X6))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.41/0.61  thf('118', plain,
% 0.41/0.61      ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['116', '117'])).
% 0.41/0.61  thf('119', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.61      inference('sup-', [status(thm)], ['113', '114'])).
% 0.41/0.61  thf('120', plain, ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B))),
% 0.41/0.61      inference('demod', [status(thm)], ['118', '119'])).
% 0.41/0.61  thf('121', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('122', plain, (((sk_E) = (sk_G))),
% 0.41/0.61      inference('clc', [status(thm)], ['120', '121'])).
% 0.41/0.61  thf('123', plain,
% 0.41/0.61      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('124', plain, (((sk_D) = (sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('125', plain,
% 0.41/0.61      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.61      inference('demod', [status(thm)], ['123', '124'])).
% 0.41/0.61  thf('126', plain,
% 0.41/0.61      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['122', '125'])).
% 0.41/0.61  thf('127', plain,
% 0.41/0.61      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['81', '126'])).
% 0.41/0.61  thf('128', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 0.41/0.61       ~
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.41/0.61      inference('sup-', [status(thm)], ['58', '127'])).
% 0.41/0.61  thf('129', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.41/0.61         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.61      inference('demod', [status(thm)], ['55', '56'])).
% 0.41/0.61  thf('130', plain,
% 0.41/0.61      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.41/0.61         <= (~
% 0.41/0.61             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 0.41/0.61      inference('split', [status(esa)], ['43'])).
% 0.41/0.61  thf('131', plain,
% 0.41/0.61      (~
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.41/0.61      inference('sup-', [status(thm)], ['129', '130'])).
% 0.41/0.61  thf('132', plain,
% 0.41/0.61      (~
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)],
% 0.41/0.61                ['45', '52', '53', '128', '131'])).
% 0.41/0.61  thf('133', plain,
% 0.41/0.61      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61          (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['35', '132'])).
% 0.41/0.61  thf('134', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 0.41/0.61         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.61      inference('demod', [status(thm)], ['37', '38'])).
% 0.41/0.61  thf('135', plain, (((sk_E) = (sk_G))),
% 0.41/0.61      inference('clc', [status(thm)], ['120', '121'])).
% 0.41/0.61  thf('136', plain,
% 0.41/0.61      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.41/0.61         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.41/0.61      inference('clc', [status(thm)], ['79', '80'])).
% 0.41/0.61  thf('137', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 0.41/0.61         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 0.41/0.61      inference('demod', [status(thm)], ['134', '135', '136'])).
% 0.41/0.61  thf('138', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 0.41/0.61       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.41/0.61      inference('split', [status(esa)], ['36'])).
% 0.41/0.61  thf('139', plain,
% 0.41/0.61      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)],
% 0.41/0.61                ['45', '52', '53', '128', '131', '138'])).
% 0.41/0.61  thf('140', plain,
% 0.41/0.61      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.61        (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['137', '139'])).
% 0.41/0.61  thf('141', plain, ($false), inference('demod', [status(thm)], ['133', '140'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
