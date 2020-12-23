%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tK8ryI3KkN

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  262 (2002 expanded)
%              Number of leaves         :   34 ( 592 expanded)
%              Depth                    :   29
%              Number of atoms          : 3584 (95608 expanded)
%              Number of equality atoms :   68 (3309 expanded)
%              Maximal formula depth    :   31 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(t125_tmap_1,conjecture,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( A
                          = ( k1_tsep_1 @ A @ D @ E ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                   => ( ( ( F = G )
                                        & ( F = H ) )
                                     => ( ( r1_tmap_1 @ A @ B @ C @ F )
                                      <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                          & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                     => ( ( ( F = G )
                                          & ( F = H ) )
                                       => ( ( r1_tmap_1 @ A @ B @ C @ F )
                                        <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                            & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('3',plain,(
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

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k2_partfun1 @ X9 @ X10 @ X8 @ X11 )
        = ( k7_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t124_tmap_1,axiom,(
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
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ! [H: $i] :
                                  ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                 => ( ( ( F = G )
                                      & ( F = H ) )
                                   => ( ( r1_tmap_1 @ ( k1_tsep_1 @ A @ D @ E ) @ B @ ( k2_tmap_1 @ A @ B @ C @ ( k1_tsep_1 @ A @ D @ E ) ) @ F )
                                    <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                        & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) @ X22 )
      | ( r1_tmap_1 @ X20 @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ X20 ) @ X26 )
      | ( X22 != X24 )
      | ( X22 != X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t124_tmap_1])).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ( r1_tmap_1 @ X20 @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ X20 ) @ X24 )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('50',plain,(
    ! [X27: $i] :
      ( ( m1_pre_topc @ X27 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','13','14','15'])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('70',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','67','68','69','70','71'])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['35','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_F = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['73','76','81','82'])).

thf('84',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('85',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['78','79'])).

thf('88',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['78','79'])).

thf('91',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('94',plain,
    ( ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['34'])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['34'])).

thf('107',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['106','110'])).

thf('112',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['22'])).

thf('113',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) @ X22 )
      | ( r1_tmap_1 @ X23 @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ X23 ) @ X24 )
      | ( X22 != X24 )
      | ( X22 != X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t124_tmap_1])).

thf('118',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ( r1_tmap_1 @ X23 @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ X23 ) @ X24 )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','118'])).

thf('120',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','126'])).

thf('128',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['65','66'])).

thf('130',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('132',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132','133'])).

thf('135',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['114','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('137',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('138',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('140',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('141',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['107'])).

thf('142',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['78','79'])).

thf('143',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['147','148'])).

thf('150',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['34'])).

thf('155',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['105','111','153','154'])).

thf('156',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['31','155'])).

thf('157',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_tmap_1 @ X20 @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ X20 ) @ X26 )
      | ~ ( r1_tmap_1 @ X23 @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ X23 ) @ X24 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) @ X22 )
      | ( X22 != X24 )
      | ( X22 != X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t124_tmap_1])).

thf('160',plain,(
    ! [X19: $i,X20: $i,X21: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X19 ) ) ) )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) @ X24 )
      | ~ ( r1_tmap_1 @ X23 @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ X23 ) @ X24 )
      | ~ ( r1_tmap_1 @ X20 @ X19 @ ( k2_tmap_1 @ X21 @ X19 @ X25 @ X20 ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k1_tsep_1 @ X21 @ X20 @ X23 ) ) )
      | ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X2 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['158','160'])).

thf('162',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X2 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X2 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X0 @ X1 ) ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X1 ) ) @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X1 ) ) )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','168'])).

thf('170',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X1 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X1 ) ) @ X0 )
      | ~ ( r1_tmap_1 @ X1 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X1 ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ sk_G )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['156','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ sk_G )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ sk_G )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_G )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ sk_G )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','174'])).

thf('176',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('177',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('178',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','67','68','69','70','71'])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('183',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('184',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['135','136','137','138'])).

thf('187',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('188',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('189',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('191',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['185','194'])).

thf('196',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['85'])).

thf('206',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['204','205'])).

thf('207',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['178','206'])).

thf('208',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
    = sk_C ),
    inference(clc,[status(thm)],['65','66'])).

thf('212',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('213',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('215',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['175','207','208','209','210','211','212','213','214'])).

thf('216',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('217',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['204'])).

thf('218',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['215','218'])).

thf('220',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['223','224'])).

thf('226',plain,(
    $false ),
    inference(demod,[status(thm)],['0','225'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tK8ryI3KkN
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 131 iterations in 0.068s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(sk_H_type, type, sk_H: $i).
% 0.20/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.53  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.53  thf(t125_tmap_1, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                 ( m1_subset_1 @
% 0.20/0.53                   C @ 
% 0.20/0.53                   ( k1_zfmisc_1 @
% 0.20/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.20/0.53                       ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.20/0.53                         ( ![F:$i]:
% 0.20/0.53                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                             ( ![G:$i]:
% 0.20/0.53                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                 ( ![H:$i]:
% 0.20/0.53                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.20/0.53                                     ( ( ( ( F ) = ( G ) ) & ( ( F ) = ( H ) ) ) =>
% 0.20/0.53                                       ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 0.20/0.53                                         ( ( r1_tmap_1 @
% 0.20/0.53                                             D @ B @ 
% 0.20/0.53                                             ( k2_tmap_1 @ A @ B @ C @ D ) @ G ) & 
% 0.20/0.53                                           ( r1_tmap_1 @
% 0.20/0.53                                             E @ B @ 
% 0.20/0.53                                             ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.53            ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53                ( l1_pre_topc @ B ) ) =>
% 0.20/0.53              ( ![C:$i]:
% 0.20/0.53                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                    ( v1_funct_2 @
% 0.20/0.53                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                    ( m1_subset_1 @
% 0.20/0.53                      C @ 
% 0.20/0.53                      ( k1_zfmisc_1 @
% 0.20/0.53                        ( k2_zfmisc_1 @
% 0.20/0.53                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53                  ( ![D:$i]:
% 0.20/0.53                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.53                      ( ![E:$i]:
% 0.20/0.53                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.20/0.53                          ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 0.20/0.53                            ( ![F:$i]:
% 0.20/0.53                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53                                ( ![G:$i]:
% 0.20/0.53                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                                    ( ![H:$i]:
% 0.20/0.53                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.20/0.53                                        ( ( ( ( F ) = ( G ) ) & 
% 0.20/0.53                                            ( ( F ) = ( H ) ) ) =>
% 0.20/0.53                                          ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 0.20/0.53                                            ( ( r1_tmap_1 @
% 0.20/0.53                                                D @ B @ 
% 0.20/0.53                                                ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 0.20/0.53                                                G ) & 
% 0.20/0.53                                              ( r1_tmap_1 @
% 0.20/0.53                                                E @ B @ 
% 0.20/0.53                                                ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 0.20/0.53                                                H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t125_tmap_1])).
% 0.20/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d4_tmap_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                 ( m1_subset_1 @
% 0.20/0.53                   C @ 
% 0.20/0.53                   ( k1_zfmisc_1 @
% 0.20/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.53                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.53                     ( k2_partfun1 @
% 0.20/0.53                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.53                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X15)
% 0.20/0.53          | ~ (v2_pre_topc @ X15)
% 0.20/0.53          | ~ (l1_pre_topc @ X15)
% 0.20/0.53          | ~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.53          | ((k2_tmap_1 @ X17 @ X15 @ X18 @ X16)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ 
% 0.20/0.53                 X18 @ (u1_struct_0 @ X16)))
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 0.20/0.53          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 0.20/0.53          | ~ (v1_funct_1 @ X18)
% 0.20/0.53          | ~ (l1_pre_topc @ X17)
% 0.20/0.53          | ~ (v2_pre_topc @ X17)
% 0.20/0.53          | (v2_struct_0 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.53                 sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k2_partfun1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.20/0.53          | ~ (v1_funct_1 @ X8)
% 0.20/0.53          | ((k2_partfun1 @ X9 @ X10 @ X8 @ X11) = (k7_relat_1 @ X8 @ X11)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53            X0) = (k7_relat_1 @ sk_C @ X0))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.53           X0) = (k7_relat_1 @ sk_C @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.53              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.53            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '16'])).
% 0.20/0.53  thf('18', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.53            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))),
% 0.20/0.53      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.53         sk_G)
% 0.20/0.53        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.53         sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['22'])).
% 0.20/0.53  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.53              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.53            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.53            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))),
% 0.20/0.53      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53         (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['23', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.53         sk_G)
% 0.20/0.53        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('33', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.53         sk_G)
% 0.20/0.53        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['34'])).
% 0.20/0.53  thf('36', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t124_tmap_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.53             ( l1_pre_topc @ B ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.53                 ( m1_subset_1 @
% 0.20/0.53                   C @ 
% 0.20/0.53                   ( k1_zfmisc_1 @
% 0.20/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.53               ( ![D:$i]:
% 0.20/0.53                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 0.20/0.53                       ( ![F:$i]:
% 0.20/0.53                         ( ( m1_subset_1 @
% 0.20/0.53                             F @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ D @ E ) ) ) =>
% 0.20/0.53                           ( ![G:$i]:
% 0.20/0.53                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.53                               ( ![H:$i]:
% 0.20/0.53                                 ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 0.20/0.53                                   ( ( ( ( F ) = ( G ) ) & ( ( F ) = ( H ) ) ) =>
% 0.20/0.53                                     ( ( r1_tmap_1 @
% 0.20/0.53                                         ( k1_tsep_1 @ A @ D @ E ) @ B @ 
% 0.20/0.53                                         ( k2_tmap_1 @
% 0.20/0.53                                           A @ B @ C @ 
% 0.20/0.53                                           ( k1_tsep_1 @ A @ D @ E ) ) @ 
% 0.20/0.53                                         F ) <=>
% 0.20/0.53                                       ( ( r1_tmap_1 @
% 0.20/0.53                                           D @ B @ 
% 0.20/0.53                                           ( k2_tmap_1 @ A @ B @ C @ D ) @ G ) & 
% 0.20/0.53                                         ( r1_tmap_1 @
% 0.20/0.53                                           E @ B @ 
% 0.20/0.53                                           ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.53         X26 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X20)
% 0.20/0.53          | ~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ X21 @ X20 @ X23)))
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.53          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X21 @ X20 @ X23) @ X19 @ 
% 0.20/0.53               (k2_tmap_1 @ X21 @ X19 @ X25 @ (k1_tsep_1 @ X21 @ X20 @ X23)) @ 
% 0.20/0.53               X22)
% 0.20/0.53          | (r1_tmap_1 @ X20 @ X19 @ (k2_tmap_1 @ X21 @ X19 @ X25 @ X20) @ X26)
% 0.20/0.53          | ((X22) != (X24))
% 0.20/0.53          | ((X22) != (X26))
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X20))
% 0.20/0.53          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.53          | (v2_struct_0 @ X23)
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.20/0.53          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (v1_funct_1 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X21)
% 0.20/0.53          | ~ (v2_pre_topc @ X21)
% 0.20/0.53          | (v2_struct_0 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t124_tmap_1])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X21)
% 0.20/0.53          | ~ (v2_pre_topc @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X21)
% 0.20/0.53          | ~ (v1_funct_1 @ X25)
% 0.20/0.53          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.20/0.53          | (v2_struct_0 @ X23)
% 0.20/0.53          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X20))
% 0.20/0.53          | (r1_tmap_1 @ X20 @ X19 @ (k2_tmap_1 @ X21 @ X19 @ X25 @ X20) @ X24)
% 0.20/0.53          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X21 @ X20 @ X23) @ X19 @ 
% 0.20/0.53               (k2_tmap_1 @ X21 @ X19 @ X25 @ (k1_tsep_1 @ X21 @ X20 @ X23)) @ 
% 0.20/0.53               X24)
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ X21 @ X20 @ X23)))
% 0.20/0.53          | ~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | (v2_struct_0 @ X20)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X19))),
% 0.20/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.20/0.53               X2)
% 0.20/0.53          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '39'])).
% 0.20/0.53  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.20/0.53               X2)
% 0.20/0.53          | (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['40', '41', '42', '43', '44', '45', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_A @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.20/0.53             X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_E)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '47'])).
% 0.20/0.53  thf('49', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t2_tsep_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X27 : $i]: ((m1_pre_topc @ X27 @ X27) | ~ (l1_pre_topc @ X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.53              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['4', '5', '6', '7', '8', '13', '14', '15'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_B)
% 0.20/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 0.20/0.53            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.53         ((v4_relat_1 @ X5 @ X6)
% 0.20/0.53          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('56', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.53  thf(t209_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) = (k7_relat_1 @ X0 @ X1))
% 0.20/0.53          | ~ (v4_relat_1 @ X0 @ X1)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.53        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( v1_relat_1 @ C ) ))).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         ((v1_relat_1 @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.53  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['58', '61'])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['52', '53', '62'])).
% 0.20/0.53  thf('64', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C)))),
% 0.20/0.53      inference('clc', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('67', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('68', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('70', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('71', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_E)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['48', '49', '67', '68', '69', '70', '71'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.20/0.53         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53            (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '72'])).
% 0.20/0.53  thf('74', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('76', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('78', plain, (((sk_F) = (sk_H))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('79', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('80', plain, (((sk_H) = (sk_G))),
% 0.20/0.53      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('81', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.20/0.53      inference('demod', [status(thm)], ['77', '80'])).
% 0.20/0.53  thf('82', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53            (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['73', '76', '81', '82'])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53         sk_H)
% 0.20/0.53        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53         sk_H))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('split', [status(esa)], ['85'])).
% 0.20/0.53  thf('87', plain, (((sk_H) = (sk_G))),
% 0.20/0.53      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53         sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53           sk_H)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('90', plain, (((sk_H) = (sk_G))),
% 0.20/0.53      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('91', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53           sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.53      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      (((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.53         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['88', '92'])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      (((~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53            (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)
% 0.20/0.53         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['84', '93'])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)
% 0.20/0.53         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['83', '94'])).
% 0.20/0.53  thf('96', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['34'])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.53  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('101', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('clc', [status(thm)], ['99', '100'])).
% 0.20/0.53  thf('102', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('clc', [status(thm)], ['101', '102'])).
% 0.20/0.53  thf('104', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53         sk_H))),
% 0.20/0.53      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.53  thf('106', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 0.20/0.53      inference('split', [status(esa)], ['34'])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53           sk_H)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('split', [status(esa)], ['107'])).
% 0.20/0.53  thf('109', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.53  thf('111', plain,
% 0.20/0.53      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('sup-', [status(thm)], ['106', '110'])).
% 0.20/0.53  thf('112', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('split', [status(esa)], ['22'])).
% 0.20/0.53  thf('113', plain, (((sk_F) = (sk_G))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('114', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['112', '113'])).
% 0.20/0.53  thf('115', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('116', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('117', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.53         X26 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X20)
% 0.20/0.53          | ~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ X21 @ X20 @ X23)))
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.53          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X21 @ X20 @ X23) @ X19 @ 
% 0.20/0.53               (k2_tmap_1 @ X21 @ X19 @ X25 @ (k1_tsep_1 @ X21 @ X20 @ X23)) @ 
% 0.20/0.53               X22)
% 0.20/0.53          | (r1_tmap_1 @ X23 @ X19 @ (k2_tmap_1 @ X21 @ X19 @ X25 @ X23) @ X24)
% 0.20/0.53          | ((X22) != (X24))
% 0.20/0.53          | ((X22) != (X26))
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X20))
% 0.20/0.53          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.53          | (v2_struct_0 @ X23)
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.20/0.53          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (v1_funct_1 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X21)
% 0.20/0.53          | ~ (v2_pre_topc @ X21)
% 0.20/0.53          | (v2_struct_0 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t124_tmap_1])).
% 0.20/0.53  thf('118', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X21)
% 0.20/0.53          | ~ (v2_pre_topc @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X21)
% 0.20/0.53          | ~ (v1_funct_1 @ X25)
% 0.20/0.53          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.20/0.53          | (v2_struct_0 @ X23)
% 0.20/0.53          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X20))
% 0.20/0.53          | (r1_tmap_1 @ X23 @ X19 @ (k2_tmap_1 @ X21 @ X19 @ X25 @ X23) @ X24)
% 0.20/0.53          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X21 @ X20 @ X23) @ X19 @ 
% 0.20/0.53               (k2_tmap_1 @ X21 @ X19 @ X25 @ (k1_tsep_1 @ X21 @ X20 @ X23)) @ 
% 0.20/0.53               X24)
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ X21 @ X20 @ X23)))
% 0.20/0.53          | ~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | (v2_struct_0 @ X20)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X19))),
% 0.20/0.53      inference('simplify', [status(thm)], ['117'])).
% 0.20/0.53  thf('119', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.20/0.53               X2)
% 0.20/0.53          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['116', '118'])).
% 0.20/0.53  thf('120', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('121', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('126', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.20/0.53               X2)
% 0.20/0.53          | (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['119', '120', '121', '122', '123', '124', '125'])).
% 0.20/0.53  thf('127', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_A @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.20/0.53             X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_E)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['115', '126'])).
% 0.20/0.53  thf('128', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('129', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('130', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('131', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('132', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('133', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('134', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_E)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53             (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['127', '128', '129', '130', '131', '132', '133'])).
% 0.20/0.53  thf('135', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.20/0.53         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53            (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_G)
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['114', '134'])).
% 0.20/0.53  thf('136', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('137', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.20/0.53      inference('demod', [status(thm)], ['77', '80'])).
% 0.20/0.53  thf('138', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('139', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53            (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_G)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 0.20/0.53  thf('140', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('141', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53           sk_H))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('split', [status(esa)], ['107'])).
% 0.20/0.53  thf('142', plain, (((sk_H) = (sk_G))),
% 0.20/0.53      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.53  thf('143', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53           sk_G))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['141', '142'])).
% 0.20/0.53  thf('144', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53           (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_G))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['140', '143'])).
% 0.20/0.53  thf('145', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['139', '144'])).
% 0.20/0.53  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('147', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['145', '146'])).
% 0.20/0.53  thf('148', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('149', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('clc', [status(thm)], ['147', '148'])).
% 0.20/0.53  thf('150', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('151', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 0.20/0.53             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('clc', [status(thm)], ['149', '150'])).
% 0.20/0.53  thf('152', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('153', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53         sk_H)) | 
% 0.20/0.53       ~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('sup-', [status(thm)], ['151', '152'])).
% 0.20/0.53  thf('154', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.53         sk_G)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.53      inference('split', [status(esa)], ['34'])).
% 0.20/0.53  thf('155', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.53         sk_G))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['105', '111', '153', '154'])).
% 0.20/0.53  thf('156', plain,
% 0.20/0.53      ((r1_tmap_1 @ sk_D @ sk_B @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 0.20/0.53        sk_G)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['31', '155'])).
% 0.20/0.53  thf('157', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('158', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ 
% 0.20/0.53        (k1_zfmisc_1 @ 
% 0.20/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('159', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.20/0.53         X26 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X20)
% 0.20/0.53          | ~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ X21 @ X20 @ X23)))
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.53          | ~ (r1_tmap_1 @ X20 @ X19 @ (k2_tmap_1 @ X21 @ X19 @ X25 @ X20) @ 
% 0.20/0.53               X26)
% 0.20/0.53          | ~ (r1_tmap_1 @ X23 @ X19 @ (k2_tmap_1 @ X21 @ X19 @ X25 @ X23) @ 
% 0.20/0.53               X24)
% 0.20/0.53          | (r1_tmap_1 @ (k1_tsep_1 @ X21 @ X20 @ X23) @ X19 @ 
% 0.20/0.53             (k2_tmap_1 @ X21 @ X19 @ X25 @ (k1_tsep_1 @ X21 @ X20 @ X23)) @ 
% 0.20/0.53             X22)
% 0.20/0.53          | ((X22) != (X24))
% 0.20/0.53          | ((X22) != (X26))
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X20))
% 0.20/0.53          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.53          | (v2_struct_0 @ X23)
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.20/0.53          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (v1_funct_1 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X21)
% 0.20/0.53          | ~ (v2_pre_topc @ X21)
% 0.20/0.53          | (v2_struct_0 @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t124_tmap_1])).
% 0.20/0.53  thf('160', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         ((v2_struct_0 @ X21)
% 0.20/0.53          | ~ (v2_pre_topc @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X21)
% 0.20/0.53          | ~ (v1_funct_1 @ X25)
% 0.20/0.53          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ 
% 0.20/0.53               (k1_zfmisc_1 @ 
% 0.20/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X19))))
% 0.20/0.53          | (v2_struct_0 @ X23)
% 0.20/0.53          | ~ (m1_pre_topc @ X23 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X20))
% 0.20/0.53          | (r1_tmap_1 @ (k1_tsep_1 @ X21 @ X20 @ X23) @ X19 @ 
% 0.20/0.53             (k2_tmap_1 @ X21 @ X19 @ X25 @ (k1_tsep_1 @ X21 @ X20 @ X23)) @ 
% 0.20/0.53             X24)
% 0.20/0.53          | ~ (r1_tmap_1 @ X23 @ X19 @ (k2_tmap_1 @ X21 @ X19 @ X25 @ X23) @ 
% 0.20/0.53               X24)
% 0.20/0.53          | ~ (r1_tmap_1 @ X20 @ X19 @ (k2_tmap_1 @ X21 @ X19 @ X25 @ X20) @ 
% 0.20/0.53               X24)
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ X21 @ X20 @ X23)))
% 0.20/0.53          | ~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | (v2_struct_0 @ X20)
% 0.20/0.53          | ~ (l1_pre_topc @ X19)
% 0.20/0.53          | ~ (v2_pre_topc @ X19)
% 0.20/0.53          | (v2_struct_0 @ X19))),
% 0.20/0.53      inference('simplify', [status(thm)], ['159'])).
% 0.20/0.53  thf('161', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.53               X2)
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.20/0.53               X2)
% 0.20/0.53          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.20/0.53             X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['158', '160'])).
% 0.20/0.53  thf('162', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('163', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('164', plain,
% 0.20/0.53      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('168', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X0 @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.53               X2)
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.20/0.53               X2)
% 0.20/0.53          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ X0 @ X1) @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X0 @ X1)) @ 
% 0.20/0.53             X2)
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['161', '162', '163', '164', '165', '166', '167'])).
% 0.20/0.53  thf('169', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X1) @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X1)) @ 
% 0.20/0.53             X0)
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.20/0.53               X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X1)))
% 0.20/0.53          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['157', '168'])).
% 0.20/0.53  thf('170', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('171', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X1)
% 0.20/0.53          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X1) @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X1)) @ 
% 0.20/0.53             X0)
% 0.20/0.53          | ~ (r1_tmap_1 @ X1 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ 
% 0.20/0.53               X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X1)))
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['169', '170'])).
% 0.20/0.53  thf('172', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_G @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 0.20/0.53          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.53               sk_G)
% 0.20/0.53          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.20/0.53             sk_G)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['156', '171'])).
% 0.20/0.53  thf('173', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('174', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_B)
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | ~ (m1_subset_1 @ sk_G @ 
% 0.20/0.53               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ X0)))
% 0.20/0.53          | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ X0))
% 0.20/0.53          | ~ (r1_tmap_1 @ X0 @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.53               sk_G)
% 0.20/0.53          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 0.20/0.53             sk_G)
% 0.20/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['172', '173'])).
% 0.20/0.53  thf('175', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53           (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_G)
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_E)
% 0.20/0.53        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 0.20/0.53        | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B @ 
% 0.20/0.53           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 0.20/0.53           sk_G)
% 0.20/0.53        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_G @ 
% 0.20/0.53             (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '174'])).
% 0.20/0.53  thf('176', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53         sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.53  thf('177', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('178', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53         (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 0.20/0.53      inference('demod', [status(thm)], ['176', '177'])).
% 0.20/0.53  thf('179', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['112', '113'])).
% 0.20/0.53  thf('180', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 0.20/0.53          | (v2_struct_0 @ sk_A)
% 0.20/0.53          | (v2_struct_0 @ sk_E)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.53          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | (v2_struct_0 @ sk_D)
% 0.20/0.53          | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['48', '49', '67', '68', '69', '70', '71'])).
% 0.20/0.53  thf('181', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 0.20/0.53         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53            (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)
% 0.20/0.53         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['179', '180'])).
% 0.20/0.53  thf('182', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('183', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.20/0.53      inference('demod', [status(thm)], ['77', '80'])).
% 0.20/0.53  thf('184', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('185', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53            (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 0.20/0.53  thf('186', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53            (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_G)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['135', '136', '137', '138'])).
% 0.20/0.53  thf('187', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53           sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.53      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.20/0.53  thf('188', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 0.20/0.53      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('189', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53           sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.53      inference('demod', [status(thm)], ['187', '188'])).
% 0.20/0.53  thf('190', plain,
% 0.20/0.53      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.20/0.53         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 0.20/0.53      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('191', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 0.20/0.53           (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53             (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)
% 0.20/0.53        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 0.20/0.53      inference('demod', [status(thm)], ['189', '190'])).
% 0.20/0.53  thf('192', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)
% 0.20/0.53         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.53         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53              (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['186', '191'])).
% 0.20/0.53  thf('193', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['112', '113'])).
% 0.20/0.53  thf('194', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)
% 0.20/0.53         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.20/0.53              (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_G)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['192', '193'])).
% 0.20/0.53  thf('195', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['185', '194'])).
% 0.20/0.53  thf('196', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B)
% 0.20/0.53         | (v2_struct_0 @ sk_D)
% 0.20/0.53         | (v2_struct_0 @ sk_E)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['195'])).
% 0.20/0.53  thf('197', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('198', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['196', '197'])).
% 0.20/0.53  thf('199', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('200', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.20/0.53         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('clc', [status(thm)], ['198', '199'])).
% 0.20/0.53  thf('201', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('202', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_D)) <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('clc', [status(thm)], ['200', '201'])).
% 0.20/0.53  thf('203', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('204', plain, (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('sup-', [status(thm)], ['202', '203'])).
% 0.20/0.53  thf('205', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53         sk_H)) | 
% 0.20/0.53       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('split', [status(esa)], ['85'])).
% 0.20/0.53  thf('206', plain,
% 0.20/0.53      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.20/0.53         sk_H))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['204', '205'])).
% 0.20/0.53  thf('207', plain,
% 0.20/0.53      ((r1_tmap_1 @ sk_E @ sk_B @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 0.20/0.53        sk_G)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['178', '206'])).
% 0.20/0.53  thf('208', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('209', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('210', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('211', plain, (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))),
% 0.20/0.53      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('212', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 0.20/0.53      inference('demod', [status(thm)], ['77', '80'])).
% 0.20/0.53  thf('213', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('214', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('215', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_E)
% 0.20/0.53        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)],
% 0.20/0.53                ['175', '207', '208', '209', '210', '211', '212', '213', '214'])).
% 0.20/0.53  thf('216', plain,
% 0.20/0.53      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 0.20/0.53         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 0.20/0.53      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.53  thf('217', plain, (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['204'])).
% 0.20/0.53  thf('218', plain, (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['216', '217'])).
% 0.20/0.53  thf('219', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_D)
% 0.20/0.53        | (v2_struct_0 @ sk_E)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['215', '218'])).
% 0.20/0.53  thf('220', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('221', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['219', '220'])).
% 0.20/0.53  thf('222', plain, (~ (v2_struct_0 @ sk_E)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('223', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 0.20/0.53      inference('clc', [status(thm)], ['221', '222'])).
% 0.20/0.53  thf('224', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('225', plain, ((v2_struct_0 @ sk_D)),
% 0.20/0.53      inference('clc', [status(thm)], ['223', '224'])).
% 0.20/0.53  thf('226', plain, ($false), inference('demod', [status(thm)], ['0', '225'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
