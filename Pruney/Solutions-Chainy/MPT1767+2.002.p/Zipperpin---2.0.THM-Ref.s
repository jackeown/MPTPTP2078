%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jW4DFXgh8d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:06 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 458 expanded)
%              Number of leaves         :   29 ( 148 expanded)
%              Depth                    :   36
%              Number of atoms          : 2850 (15669 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t78_tmap_1,conjecture,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

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
                       => ( ( m1_pre_topc @ C @ D )
                         => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t78_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) )
        & ( l1_struct_0 @ D ) )
     => ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X13 @ X14 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','7','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X13 @ X14 @ X12 @ X15 ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('19',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('23',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('24',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('25',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ X18 @ ( k3_tmap_1 @ X20 @ X17 @ X19 @ X19 @ X18 ) )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t74_tmap_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_E ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('36',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X10 )
      | ( ( k3_tmap_1 @ X9 @ X7 @ X10 @ X8 @ X11 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X7 ) @ X11 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X11 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( m1_pre_topc @ X16 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('54',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_pre_topc @ X4 @ X5 )
      | ( ( k2_tmap_1 @ X5 @ X3 @ X6 @ X4 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) @ X6 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60','61','62'])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E )
    = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','75','76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t77_tmap_1,axiom,(
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
                         => ( ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ F @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                              & ( m1_pre_topc @ D @ C ) )
                           => ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X24 ) @ ( k2_tmap_1 @ X23 @ X21 @ X26 @ X22 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) @ X24 @ ( k2_tmap_1 @ X23 @ X21 @ X26 @ X25 ) )
      | ~ ( m1_pre_topc @ X22 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_A )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_A ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E ) @ ( k2_tmap_1 @ X0 @ sk_B @ X1 @ X2 ) )
      | ~ ( m1_pre_topc @ X2 @ X0 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','102'])).

thf('104',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60','61','62'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['110','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['103','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X15 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X13 @ X14 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('124',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('125',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X24 ) @ ( k2_tmap_1 @ X23 @ X21 @ X26 @ X22 ) )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X21 ) @ X24 @ ( k2_tmap_1 @ X23 @ X21 @ X26 @ X25 ) )
      | ~ ( m1_pre_topc @ X22 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t77_tmap_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X1 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( m1_pre_topc @ X3 @ X0 )
      | ~ ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X0 ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ X1 @ sk_B @ X2 @ X3 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X3 @ X1 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['119','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('141',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('142',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('146',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138','139','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','148'])).

thf('150',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['144','145'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','151'])).

thf('153',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['144','145'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','154'])).

thf('156',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    $false ),
    inference(demod,[status(thm)],['0','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jW4DFXgh8d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 335 iterations in 0.283s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.53/0.75  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.53/0.75  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.53/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.75  thf(sk_E_type, type, sk_E: $i).
% 0.53/0.75  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.53/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.75  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.75  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.53/0.75  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.53/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.75  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.53/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.75  thf(t78_tmap_1, conjecture,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.75             ( l1_pre_topc @ B ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.53/0.75               ( ![D:$i]:
% 0.53/0.75                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.53/0.75                   ( ![E:$i]:
% 0.53/0.75                     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.75                         ( v1_funct_2 @
% 0.53/0.75                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.75                         ( m1_subset_1 @
% 0.53/0.75                           E @ 
% 0.53/0.75                           ( k1_zfmisc_1 @
% 0.53/0.75                             ( k2_zfmisc_1 @
% 0.53/0.75                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.75                       ( ( m1_pre_topc @ C @ D ) =>
% 0.53/0.75                         ( r2_funct_2 @
% 0.53/0.75                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.53/0.75                           ( k3_tmap_1 @
% 0.53/0.75                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.53/0.75                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.75    (~( ![A:$i]:
% 0.53/0.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.53/0.75            ( l1_pre_topc @ A ) ) =>
% 0.53/0.75          ( ![B:$i]:
% 0.53/0.75            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.75                ( l1_pre_topc @ B ) ) =>
% 0.53/0.75              ( ![C:$i]:
% 0.53/0.75                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.53/0.75                  ( ![D:$i]:
% 0.53/0.75                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.53/0.75                      ( ![E:$i]:
% 0.53/0.75                        ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.75                            ( v1_funct_2 @
% 0.53/0.75                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.75                            ( m1_subset_1 @
% 0.53/0.75                              E @ 
% 0.53/0.75                              ( k1_zfmisc_1 @
% 0.53/0.75                                ( k2_zfmisc_1 @
% 0.53/0.75                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.75                          ( ( m1_pre_topc @ C @ D ) =>
% 0.53/0.75                            ( r2_funct_2 @
% 0.53/0.75                              ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.53/0.75                              ( k3_tmap_1 @
% 0.53/0.75                                A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.53/0.75                              ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t78_tmap_1])).
% 0.53/0.75  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(dt_k2_tmap_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.75     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 0.53/0.75         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.75         ( m1_subset_1 @
% 0.53/0.75           C @ 
% 0.53/0.75           ( k1_zfmisc_1 @
% 0.53/0.75             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.53/0.75         ( l1_struct_0 @ D ) ) =>
% 0.53/0.75       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 0.53/0.75         ( v1_funct_2 @
% 0.53/0.75           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.53/0.75           ( u1_struct_0 @ B ) ) & 
% 0.53/0.75         ( m1_subset_1 @
% 0.53/0.75           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.53/0.75           ( k1_zfmisc_1 @
% 0.53/0.75             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X12 @ 
% 0.53/0.75             (k1_zfmisc_1 @ 
% 0.53/0.75              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14))))
% 0.53/0.75          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14))
% 0.53/0.75          | ~ (v1_funct_1 @ X12)
% 0.53/0.75          | ~ (l1_struct_0 @ X14)
% 0.53/0.75          | ~ (l1_struct_0 @ X13)
% 0.53/0.75          | ~ (l1_struct_0 @ X15)
% 0.53/0.75          | (v1_funct_1 @ (k2_tmap_1 @ X13 @ X14 @ X12 @ X15)))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.53/0.75  thf('4', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (l1_struct_0 @ X0)
% 0.53/0.75          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l1_struct_0 @ sk_B)
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.75  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(dt_l1_pre_topc, axiom,
% 0.53/0.75    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.53/0.75  thf('6', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.53/0.75  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.75  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('9', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.53/0.75  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('12', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (l1_struct_0 @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['4', '7', '10', '11', '12'])).
% 0.53/0.75  thf('14', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('15', plain,
% 0.53/0.75      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X12 @ 
% 0.53/0.75             (k1_zfmisc_1 @ 
% 0.53/0.75              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14))))
% 0.53/0.75          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14))
% 0.53/0.75          | ~ (v1_funct_1 @ X12)
% 0.53/0.75          | ~ (l1_struct_0 @ X14)
% 0.53/0.75          | ~ (l1_struct_0 @ X13)
% 0.53/0.75          | ~ (l1_struct_0 @ X15)
% 0.53/0.75          | (v1_funct_2 @ (k2_tmap_1 @ X13 @ X14 @ X12 @ X15) @ 
% 0.53/0.75             (u1_struct_0 @ X15) @ (u1_struct_0 @ X14)))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.53/0.75           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (l1_struct_0 @ X0)
% 0.53/0.75          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l1_struct_0 @ sk_B)
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.75  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.75  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('19', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('20', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('21', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.53/0.75           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (l1_struct_0 @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.53/0.75  thf('22', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t2_tsep_1, axiom,
% 0.53/0.75    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.53/0.75  thf('23', plain,
% 0.53/0.75      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.53/0.75  thf('25', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t74_tmap_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.75             ( l1_pre_topc @ B ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.53/0.75               ( ![D:$i]:
% 0.53/0.75                 ( ( ( v1_funct_1 @ D ) & 
% 0.53/0.75                     ( v1_funct_2 @
% 0.53/0.75                       D @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.75                     ( m1_subset_1 @
% 0.53/0.75                       D @ 
% 0.53/0.75                       ( k1_zfmisc_1 @
% 0.53/0.75                         ( k2_zfmisc_1 @
% 0.53/0.75                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.75                   ( r2_funct_2 @
% 0.53/0.75                     ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ 
% 0.53/0.75                     ( k3_tmap_1 @ A @ B @ C @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('26', plain,
% 0.53/0.75      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X17)
% 0.53/0.75          | ~ (v2_pre_topc @ X17)
% 0.53/0.75          | ~ (l1_pre_topc @ X17)
% 0.53/0.75          | ~ (v1_funct_1 @ X18)
% 0.53/0.75          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))
% 0.53/0.75          | ~ (m1_subset_1 @ X18 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17) @ X18 @ 
% 0.53/0.75             (k3_tmap_1 @ X20 @ X17 @ X19 @ X19 @ X18))
% 0.53/0.75          | ~ (m1_pre_topc @ X19 @ X20)
% 0.53/0.75          | (v2_struct_0 @ X19)
% 0.53/0.75          | ~ (l1_pre_topc @ X20)
% 0.53/0.75          | ~ (v2_pre_topc @ X20)
% 0.53/0.75          | (v2_struct_0 @ X20))),
% 0.53/0.75      inference('cnf', [status(esa)], [t74_tmap_1])).
% 0.53/0.75  thf('27', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v2_pre_topc @ X0)
% 0.53/0.75          | ~ (l1_pre_topc @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_E))
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('29', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('32', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v2_pre_topc @ X0)
% 0.53/0.75          | ~ (l1_pre_topc @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ sk_A @ sk_E))
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.53/0.75  thf('33', plain,
% 0.53/0.75      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.75        | (v2_struct_0 @ sk_B)
% 0.53/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E))
% 0.53/0.75        | (v2_struct_0 @ sk_A)
% 0.53/0.75        | ~ (l1_pre_topc @ sk_A)
% 0.53/0.75        | ~ (v2_pre_topc @ sk_A)
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['24', '32'])).
% 0.53/0.75  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('35', plain,
% 0.53/0.75      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.53/0.75  thf('36', plain,
% 0.53/0.75      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.53/0.75  thf('37', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(d5_tmap_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.75             ( l1_pre_topc @ B ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( m1_pre_topc @ C @ A ) =>
% 0.53/0.75               ( ![D:$i]:
% 0.53/0.75                 ( ( m1_pre_topc @ D @ A ) =>
% 0.53/0.75                   ( ![E:$i]:
% 0.53/0.75                     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.75                         ( v1_funct_2 @
% 0.53/0.75                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.75                         ( m1_subset_1 @
% 0.53/0.75                           E @ 
% 0.53/0.75                           ( k1_zfmisc_1 @
% 0.53/0.75                             ( k2_zfmisc_1 @
% 0.53/0.75                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.75                       ( ( m1_pre_topc @ D @ C ) =>
% 0.53/0.75                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.53/0.75                           ( k2_partfun1 @
% 0.53/0.75                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.53/0.75                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('38', plain,
% 0.53/0.75      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X7)
% 0.53/0.75          | ~ (v2_pre_topc @ X7)
% 0.53/0.75          | ~ (l1_pre_topc @ X7)
% 0.53/0.75          | ~ (m1_pre_topc @ X8 @ X9)
% 0.53/0.75          | ~ (m1_pre_topc @ X8 @ X10)
% 0.53/0.75          | ((k3_tmap_1 @ X9 @ X7 @ X10 @ X8 @ X11)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X7) @ 
% 0.53/0.75                 X11 @ (u1_struct_0 @ X8)))
% 0.53/0.75          | ~ (m1_subset_1 @ X11 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X7))))
% 0.53/0.75          | ~ (v1_funct_2 @ X11 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X7))
% 0.53/0.75          | ~ (v1_funct_1 @ X11)
% 0.53/0.75          | ~ (m1_pre_topc @ X10 @ X9)
% 0.53/0.75          | ~ (l1_pre_topc @ X9)
% 0.53/0.75          | ~ (v2_pre_topc @ X9)
% 0.53/0.75          | (v2_struct_0 @ X9))),
% 0.53/0.75      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.53/0.75  thf('39', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v2_pre_topc @ X0)
% 0.53/0.75          | ~ (l1_pre_topc @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X1)))
% 0.53/0.75          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['37', '38'])).
% 0.53/0.75  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('41', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('44', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v2_pre_topc @ X0)
% 0.53/0.75          | ~ (l1_pre_topc @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.53/0.75          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X1)))
% 0.53/0.75          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ X1 @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.53/0.75  thf('45', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (l1_pre_topc @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_B)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (l1_pre_topc @ sk_A)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['36', '44'])).
% 0.53/0.75  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('49', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_B)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X0)))
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.53/0.75  thf('50', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('simplify', [status(thm)], ['49'])).
% 0.53/0.75  thf('51', plain,
% 0.53/0.75      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.75        | (v2_struct_0 @ sk_B)
% 0.53/0.75        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E)
% 0.53/0.75            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (u1_struct_0 @ sk_A)))
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['35', '50'])).
% 0.53/0.75  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('53', plain,
% 0.53/0.75      (![X16 : $i]: ((m1_pre_topc @ X16 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.53/0.75  thf('54', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(d4_tmap_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.75             ( l1_pre_topc @ B ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( ( v1_funct_1 @ C ) & 
% 0.53/0.75                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.75                 ( m1_subset_1 @
% 0.53/0.75                   C @ 
% 0.53/0.75                   ( k1_zfmisc_1 @
% 0.53/0.75                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.75               ( ![D:$i]:
% 0.53/0.75                 ( ( m1_pre_topc @ D @ A ) =>
% 0.53/0.75                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.53/0.75                     ( k2_partfun1 @
% 0.53/0.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.53/0.75                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('55', plain,
% 0.53/0.75      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X3)
% 0.53/0.75          | ~ (v2_pre_topc @ X3)
% 0.53/0.75          | ~ (l1_pre_topc @ X3)
% 0.53/0.75          | ~ (m1_pre_topc @ X4 @ X5)
% 0.53/0.75          | ((k2_tmap_1 @ X5 @ X3 @ X6 @ X4)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3) @ X6 @ 
% 0.53/0.75                 (u1_struct_0 @ X4)))
% 0.53/0.75          | ~ (m1_subset_1 @ X6 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))))
% 0.53/0.75          | ~ (v1_funct_2 @ X6 @ (u1_struct_0 @ X5) @ (u1_struct_0 @ X3))
% 0.53/0.75          | ~ (v1_funct_1 @ X6)
% 0.53/0.75          | ~ (l1_pre_topc @ X5)
% 0.53/0.75          | ~ (v2_pre_topc @ X5)
% 0.53/0.75          | (v2_struct_0 @ X5))),
% 0.53/0.75      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.53/0.75  thf('56', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_A)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_A)
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['54', '55'])).
% 0.53/0.75  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('59', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('60', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('62', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('63', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('demod', [status(thm)],
% 0.53/0.75                ['56', '57', '58', '59', '60', '61', '62'])).
% 0.53/0.75  thf('64', plain,
% 0.53/0.75      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.75        | (v2_struct_0 @ sk_B)
% 0.53/0.75        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)
% 0.53/0.75            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (u1_struct_0 @ sk_A)))
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['53', '63'])).
% 0.53/0.75  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('66', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_B)
% 0.53/0.75        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)
% 0.53/0.75            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (u1_struct_0 @ sk_A)))
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['64', '65'])).
% 0.53/0.75  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('68', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)
% 0.53/0.75            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('clc', [status(thm)], ['66', '67'])).
% 0.53/0.75  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('70', plain,
% 0.53/0.75      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)
% 0.53/0.75         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75            (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('clc', [status(thm)], ['68', '69'])).
% 0.53/0.75  thf('71', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_B)
% 0.53/0.75        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E)
% 0.53/0.75            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['51', '52', '70'])).
% 0.53/0.75  thf('72', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('73', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E)
% 0.53/0.75            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)))),
% 0.53/0.75      inference('clc', [status(thm)], ['71', '72'])).
% 0.53/0.75  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('75', plain,
% 0.53/0.75      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_A @ sk_E)
% 0.53/0.75         = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))),
% 0.53/0.75      inference('clc', [status(thm)], ['73', '74'])).
% 0.53/0.75  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('78', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_B)
% 0.53/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))
% 0.53/0.75        | (v2_struct_0 @ sk_A)
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['33', '34', '75', '76', '77'])).
% 0.53/0.75  thf('79', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))
% 0.53/0.75        | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('simplify', [status(thm)], ['78'])).
% 0.53/0.75  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('81', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_B)
% 0.53/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A)))),
% 0.53/0.75      inference('clc', [status(thm)], ['79', '80'])).
% 0.53/0.75  thf('82', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('83', plain,
% 0.53/0.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75        (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_A))),
% 0.53/0.75      inference('clc', [status(thm)], ['81', '82'])).
% 0.53/0.75  thf('84', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t77_tmap_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.53/0.75             ( l1_pre_topc @ B ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.53/0.75               ( ![D:$i]:
% 0.53/0.75                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.53/0.75                   ( ![E:$i]:
% 0.53/0.75                     ( ( ( v1_funct_1 @ E ) & 
% 0.53/0.75                         ( v1_funct_2 @
% 0.53/0.75                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.75                         ( m1_subset_1 @
% 0.53/0.75                           E @ 
% 0.53/0.75                           ( k1_zfmisc_1 @
% 0.53/0.75                             ( k2_zfmisc_1 @
% 0.53/0.75                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.75                       ( ![F:$i]:
% 0.53/0.75                         ( ( ( v1_funct_1 @ F ) & 
% 0.53/0.75                             ( v1_funct_2 @
% 0.53/0.75                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.53/0.75                             ( m1_subset_1 @
% 0.53/0.75                               F @ 
% 0.53/0.75                               ( k1_zfmisc_1 @
% 0.53/0.75                                 ( k2_zfmisc_1 @
% 0.53/0.75                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.53/0.75                           ( ( ( r2_funct_2 @
% 0.53/0.75                                 ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.53/0.75                                 F @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 0.53/0.75                               ( m1_pre_topc @ D @ C ) ) =>
% 0.53/0.75                             ( r2_funct_2 @
% 0.53/0.75                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.53/0.75                               ( k3_tmap_1 @ A @ B @ C @ D @ F ) @ 
% 0.53/0.75                               ( k2_tmap_1 @ A @ B @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('85', plain,
% 0.53/0.75      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X21)
% 0.53/0.75          | ~ (v2_pre_topc @ X21)
% 0.53/0.75          | ~ (l1_pre_topc @ X21)
% 0.53/0.75          | (v2_struct_0 @ X22)
% 0.53/0.75          | ~ (m1_pre_topc @ X22 @ X23)
% 0.53/0.75          | ~ (v1_funct_1 @ X24)
% 0.53/0.75          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))
% 0.53/0.75          | ~ (m1_subset_1 @ X24 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.53/0.75             (k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X24) @ 
% 0.53/0.75             (k2_tmap_1 @ X23 @ X21 @ X26 @ X22))
% 0.53/0.75          | ~ (r2_funct_2 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21) @ X24 @ 
% 0.53/0.75               (k2_tmap_1 @ X23 @ X21 @ X26 @ X25))
% 0.53/0.75          | ~ (m1_pre_topc @ X22 @ X25)
% 0.53/0.75          | ~ (m1_subset_1 @ X26 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))))
% 0.53/0.75          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))
% 0.53/0.75          | ~ (v1_funct_1 @ X26)
% 0.53/0.75          | ~ (m1_pre_topc @ X25 @ X23)
% 0.53/0.75          | (v2_struct_0 @ X25)
% 0.53/0.75          | ~ (l1_pre_topc @ X23)
% 0.53/0.75          | ~ (v2_pre_topc @ X23)
% 0.53/0.75          | (v2_struct_0 @ X23))),
% 0.53/0.75      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.53/0.75  thf('86', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v2_pre_topc @ X0)
% 0.53/0.75          | ~ (l1_pre_topc @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.53/0.75          | ~ (v1_funct_1 @ X1)
% 0.53/0.75          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (m1_subset_1 @ X1 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.53/0.75          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.53/0.75          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_A))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E) @ 
% 0.53/0.75             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (m1_pre_topc @ X2 @ X0)
% 0.53/0.75          | (v2_struct_0 @ X2)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['84', '85'])).
% 0.53/0.75  thf('87', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('90', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('91', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v2_pre_topc @ X0)
% 0.53/0.75          | ~ (l1_pre_topc @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.53/0.75          | ~ (v1_funct_1 @ X1)
% 0.53/0.75          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (m1_subset_1 @ X1 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.53/0.75          | ~ (m1_pre_topc @ X2 @ sk_A)
% 0.53/0.75          | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (k2_tmap_1 @ X0 @ sk_B @ X1 @ sk_A))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ X0 @ sk_B @ sk_A @ X2 @ sk_E) @ 
% 0.53/0.75             (k2_tmap_1 @ X0 @ sk_B @ X1 @ X2))
% 0.53/0.75          | ~ (m1_pre_topc @ X2 @ X0)
% 0.53/0.75          | (v2_struct_0 @ X2)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 0.53/0.75  thf('92', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (m1_subset_1 @ sk_E @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_A)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['83', '91'])).
% 0.53/0.75  thf('93', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('94', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('95', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('98', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['92', '93', '94', '95', '96', '97'])).
% 0.53/0.75  thf('99', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_A @ sk_A)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('simplify', [status(thm)], ['98'])).
% 0.53/0.75  thf('100', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (l1_pre_topc @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['23', '99'])).
% 0.53/0.75  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('102', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['100', '101'])).
% 0.53/0.75  thf('103', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75           (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.53/0.75        | (v2_struct_0 @ sk_D)
% 0.53/0.75        | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['22', '102'])).
% 0.53/0.75  thf('104', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('105', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('simplify', [status(thm)], ['49'])).
% 0.53/0.75  thf('106', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_B)
% 0.53/0.75        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.53/0.75            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (u1_struct_0 @ sk_D)))
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['104', '105'])).
% 0.53/0.75  thf('107', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('108', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.53/0.75            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.53/0.75      inference('clc', [status(thm)], ['106', '107'])).
% 0.53/0.75  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('110', plain,
% 0.53/0.75      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.53/0.75         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75            (u1_struct_0 @ sk_D)))),
% 0.53/0.75      inference('clc', [status(thm)], ['108', '109'])).
% 0.53/0.75  thf('111', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('112', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.53/0.75              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75                 sk_E @ (u1_struct_0 @ X0)))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('demod', [status(thm)],
% 0.53/0.75                ['56', '57', '58', '59', '60', '61', '62'])).
% 0.53/0.75  thf('113', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_B)
% 0.53/0.75        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.53/0.75            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (u1_struct_0 @ sk_D)))
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['111', '112'])).
% 0.53/0.75  thf('114', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('115', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.53/0.75            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.53/0.75      inference('clc', [status(thm)], ['113', '114'])).
% 0.53/0.75  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('117', plain,
% 0.53/0.75      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.53/0.75         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.53/0.75            (u1_struct_0 @ sk_D)))),
% 0.53/0.75      inference('clc', [status(thm)], ['115', '116'])).
% 0.53/0.75  thf('118', plain,
% 0.53/0.75      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.53/0.75         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.53/0.75      inference('sup+', [status(thm)], ['110', '117'])).
% 0.53/0.75  thf('119', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.53/0.75        | (v2_struct_0 @ sk_D)
% 0.53/0.75        | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('demod', [status(thm)], ['103', '118'])).
% 0.53/0.75  thf('120', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('121', plain,
% 0.53/0.75      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X12 @ 
% 0.53/0.75             (k1_zfmisc_1 @ 
% 0.53/0.75              (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14))))
% 0.53/0.75          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X14))
% 0.53/0.75          | ~ (v1_funct_1 @ X12)
% 0.53/0.75          | ~ (l1_struct_0 @ X14)
% 0.53/0.75          | ~ (l1_struct_0 @ X13)
% 0.53/0.75          | ~ (l1_struct_0 @ X15)
% 0.53/0.75          | (m1_subset_1 @ (k2_tmap_1 @ X13 @ X14 @ X12 @ X15) @ 
% 0.53/0.75             (k1_zfmisc_1 @ 
% 0.53/0.75              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14)))))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 0.53/0.75  thf('122', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.53/0.75           (k1_zfmisc_1 @ 
% 0.53/0.75            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.53/0.75          | ~ (l1_struct_0 @ X0)
% 0.53/0.75          | ~ (l1_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l1_struct_0 @ sk_B)
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['120', '121'])).
% 0.53/0.75  thf('123', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.75  thf('124', plain, ((l1_struct_0 @ sk_B)),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('125', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('126', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('127', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.53/0.75           (k1_zfmisc_1 @ 
% 0.53/0.75            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.53/0.75          | ~ (l1_struct_0 @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.53/0.75  thf('128', plain,
% 0.53/0.75      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X21)
% 0.53/0.75          | ~ (v2_pre_topc @ X21)
% 0.53/0.75          | ~ (l1_pre_topc @ X21)
% 0.53/0.75          | (v2_struct_0 @ X22)
% 0.53/0.75          | ~ (m1_pre_topc @ X22 @ X23)
% 0.53/0.75          | ~ (v1_funct_1 @ X24)
% 0.53/0.75          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))
% 0.53/0.75          | ~ (m1_subset_1 @ X24 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21))))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.53/0.75             (k3_tmap_1 @ X23 @ X21 @ X25 @ X22 @ X24) @ 
% 0.53/0.75             (k2_tmap_1 @ X23 @ X21 @ X26 @ X22))
% 0.53/0.75          | ~ (r2_funct_2 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X21) @ X24 @ 
% 0.53/0.75               (k2_tmap_1 @ X23 @ X21 @ X26 @ X25))
% 0.53/0.75          | ~ (m1_pre_topc @ X22 @ X25)
% 0.53/0.75          | ~ (m1_subset_1 @ X26 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))))
% 0.53/0.75          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X21))
% 0.53/0.75          | ~ (v1_funct_1 @ X26)
% 0.53/0.75          | ~ (m1_pre_topc @ X25 @ X23)
% 0.53/0.75          | (v2_struct_0 @ X25)
% 0.53/0.75          | ~ (l1_pre_topc @ X23)
% 0.53/0.75          | ~ (v2_pre_topc @ X23)
% 0.53/0.75          | (v2_struct_0 @ X23))),
% 0.53/0.75      inference('cnf', [status(esa)], [t77_tmap_1])).
% 0.53/0.75  thf('129', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.75         (~ (l1_struct_0 @ X0)
% 0.53/0.75          | (v2_struct_0 @ X1)
% 0.53/0.75          | ~ (v2_pre_topc @ X1)
% 0.53/0.75          | ~ (l1_pre_topc @ X1)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ X1)
% 0.53/0.75          | ~ (v1_funct_1 @ X2)
% 0.53/0.75          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.53/0.75          | ~ (m1_pre_topc @ X3 @ X0)
% 0.53/0.75          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.53/0.75               (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.53/0.75             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X3))
% 0.53/0.75          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.53/0.75               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X3 @ X1)
% 0.53/0.75          | (v2_struct_0 @ X3)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_B)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['127', '128'])).
% 0.53/0.75  thf('130', plain, ((l1_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('131', plain, ((v2_pre_topc @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('132', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.75         (~ (l1_struct_0 @ X0)
% 0.53/0.75          | (v2_struct_0 @ X1)
% 0.53/0.75          | ~ (v2_pre_topc @ X1)
% 0.53/0.75          | ~ (l1_pre_topc @ X1)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ X1)
% 0.53/0.75          | ~ (v1_funct_1 @ X2)
% 0.53/0.75          | ~ (v1_funct_2 @ X2 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ X1) @ (u1_struct_0 @ sk_B))))
% 0.53/0.75          | ~ (m1_pre_topc @ X3 @ X0)
% 0.53/0.75          | ~ (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.53/0.75               (k2_tmap_1 @ X1 @ sk_B @ X2 @ X0))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ X1 @ sk_B @ X0 @ X3 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.53/0.75             (k2_tmap_1 @ X1 @ sk_B @ X2 @ X3))
% 0.53/0.75          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0) @ 
% 0.53/0.75               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X3 @ X1)
% 0.53/0.75          | (v2_struct_0 @ X3)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('demod', [status(thm)], ['129', '130', '131'])).
% 0.53/0.75  thf('133', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.53/0.75          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.53/0.75               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.75          | ~ (m1_subset_1 @ sk_E @ 
% 0.53/0.75               (k1_zfmisc_1 @ 
% 0.53/0.75                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.53/0.75          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (v1_funct_1 @ sk_E)
% 0.53/0.75          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_A)
% 0.53/0.75          | ~ (v2_pre_topc @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l1_struct_0 @ sk_D))),
% 0.53/0.75      inference('sup-', [status(thm)], ['119', '132'])).
% 0.53/0.75  thf('134', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_E @ 
% 0.53/0.75        (k1_zfmisc_1 @ 
% 0.53/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('135', plain,
% 0.53/0.75      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('136', plain, ((v1_funct_1 @ sk_E)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('137', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('140', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(dt_m1_pre_topc, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l1_pre_topc @ A ) =>
% 0.53/0.75       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.53/0.75  thf('141', plain,
% 0.53/0.75      (![X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.53/0.75  thf('142', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.53/0.75      inference('sup-', [status(thm)], ['140', '141'])).
% 0.53/0.75  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('144', plain, ((l1_pre_topc @ sk_D)),
% 0.53/0.75      inference('demod', [status(thm)], ['142', '143'])).
% 0.53/0.75  thf('145', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.53/0.75  thf('146', plain, ((l1_struct_0 @ sk_D)),
% 0.53/0.75      inference('sup-', [status(thm)], ['144', '145'])).
% 0.53/0.75  thf('147', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.53/0.75          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.53/0.75               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)],
% 0.53/0.75                ['133', '134', '135', '136', '137', '138', '139', '146'])).
% 0.53/0.75  thf('148', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.53/0.75               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.53/0.75          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('simplify', [status(thm)], ['147'])).
% 0.53/0.75  thf('149', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (l1_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_D))),
% 0.53/0.75      inference('sup-', [status(thm)], ['21', '148'])).
% 0.53/0.75  thf('150', plain, ((l1_struct_0 @ sk_D)),
% 0.53/0.75      inference('sup-', [status(thm)], ['144', '145'])).
% 0.53/0.75  thf('151', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_B)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_D))),
% 0.53/0.75      inference('demod', [status(thm)], ['149', '150'])).
% 0.53/0.75  thf('152', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (l1_struct_0 @ sk_D)
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['13', '151'])).
% 0.53/0.75  thf('153', plain, ((l1_struct_0 @ sk_D)),
% 0.53/0.75      inference('sup-', [status(thm)], ['144', '145'])).
% 0.53/0.75  thf('154', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.53/0.75          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.53/0.75              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.53/0.75          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | (v2_struct_0 @ sk_A)
% 0.53/0.75          | (v2_struct_0 @ sk_D)
% 0.53/0.75          | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('demod', [status(thm)], ['152', '153'])).
% 0.53/0.75  thf('155', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_B)
% 0.53/0.75        | (v2_struct_0 @ sk_D)
% 0.53/0.75        | (v2_struct_0 @ sk_A)
% 0.53/0.75        | (v2_struct_0 @ sk_C)
% 0.53/0.75        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.53/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.53/0.75            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['1', '154'])).
% 0.53/0.75  thf('156', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('157', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_B)
% 0.53/0.75        | (v2_struct_0 @ sk_D)
% 0.53/0.75        | (v2_struct_0 @ sk_A)
% 0.53/0.75        | (v2_struct_0 @ sk_C)
% 0.53/0.75        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.53/0.75            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.53/0.75      inference('demod', [status(thm)], ['155', '156'])).
% 0.53/0.75  thf('158', plain,
% 0.53/0.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.53/0.75          (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.53/0.75           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.53/0.75          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('159', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_C)
% 0.53/0.75        | (v2_struct_0 @ sk_A)
% 0.53/0.75        | (v2_struct_0 @ sk_D)
% 0.53/0.75        | (v2_struct_0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['157', '158'])).
% 0.53/0.75  thf('160', plain, (~ (v2_struct_0 @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('161', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.53/0.75      inference('sup-', [status(thm)], ['159', '160'])).
% 0.53/0.75  thf('162', plain, (~ (v2_struct_0 @ sk_D)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('163', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('clc', [status(thm)], ['161', '162'])).
% 0.53/0.75  thf('164', plain, (~ (v2_struct_0 @ sk_C)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('165', plain, ((v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('clc', [status(thm)], ['163', '164'])).
% 0.53/0.75  thf('166', plain, ($false), inference('demod', [status(thm)], ['0', '165'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
