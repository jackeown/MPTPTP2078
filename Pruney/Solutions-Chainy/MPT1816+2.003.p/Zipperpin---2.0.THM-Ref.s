%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VmuPXsJTHp

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:07 EST 2020

% Result     : Theorem 8.82s
% Output     : Refutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :  332 (6016 expanded)
%              Number of leaves         :   37 (1799 expanded)
%              Depth                    :   34
%              Number of atoms          : 4571 (428348 expanded)
%              Number of equality atoms :   69 (3707 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t132_tmap_1,conjecture,(
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
                     => ( ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                          & ( r4_tsep_1 @ A @ D @ E ) )
                       => ( ( ( v1_funct_1 @ C )
                            & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ C @ A @ B )
                            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                       => ( ( ( A
                              = ( k1_tsep_1 @ A @ D @ E ) )
                            & ( r4_tsep_1 @ A @ D @ E ) )
                         => ( ( ( v1_funct_1 @ C )
                              & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ C @ A @ B )
                              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                          <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) )
                              & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) )
                              & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) )
                              & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B )
                              & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X20 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X20 @ X19 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
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

thf('12',plain,(
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
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( ( k2_partfun1 @ X9 @ X10 @ X8 @ X11 )
        = ( k7_relat_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k7_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf(t129_tmap_1,axiom,(
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
                 => ( ( r4_tsep_1 @ A @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( k1_tsep_1 @ A @ C @ D ) @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                        <=> ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) )
                            & ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) )
                            & ( v1_funct_2 @ ( k2_tmap_1 @ A @ B @ E @ D ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                            & ( v5_pre_topc @ ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B )
                            & ( m1_subset_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X30 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X30 ) @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X30 ) @ X30 @ X26 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X27 ) @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X27 ) @ X27 @ X26 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( r4_tsep_1 @ X28 @ X30 @ X27 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('55',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X25 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X23 @ X24 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('58',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','59','62','63','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['53','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('82',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('83',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X23 @ X24 @ X22 @ X25 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('92',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['83','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('94',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('96',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X25 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X23 @ X24 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['96','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('107',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','74','75','76','77','78','79','80','81','82','94','95','107','108','109'])).

thf('111',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['111'])).

thf('113',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('114',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('118',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['35'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('120',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','59','62','63','64'])).

thf('122',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) @ X26 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X27 ) @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( r4_tsep_1 @ X28 @ X30 @ X27 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127','128','129','130'])).

thf('132',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['120','131'])).

thf('133',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('139',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('143',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','138','139','140','141','142'])).

thf('144',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['119','143'])).

thf('145',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','146'])).

thf('148',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['117','148'])).

thf('150',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('151',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['116','151'])).

thf('153',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('154',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['154'])).

thf('156',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['153','155'])).

thf('157',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['115'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('168',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['35'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','59','62','63','64'])).

thf('171',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) @ X26 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X28 @ X30 @ X27 ) ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X28 @ X26 @ X29 @ X30 ) @ X30 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( r4_tsep_1 @ X28 @ X30 @ X27 )
      | ~ ( m1_pre_topc @ X30 @ X28 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D ) @ sk_D @ X0 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D ) @ sk_D @ X0 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['173','174','175','176','177','178','179','180','181','182','183','184'])).

thf('186',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['170','185'])).

thf('187',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('188',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188','189','190','191','192','193'])).

thf('195',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','194'])).

thf('196',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['168','197'])).

thf('199',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['167','199'])).

thf('201',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('202',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['166','202'])).

thf('204',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('205',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['205'])).

thf('207',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup+',[status(thm)],['204','206'])).

thf('208',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('210',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','59','62','63','64'])).

thf('212',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('215',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('219',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['212','219'])).

thf('221',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('222',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('223',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88','89','90'])).

thf('225',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['217','218'])).

thf('227',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('229',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('231',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['217','218'])).

thf('233',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('235',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('236',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('237',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('238',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('239',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('240',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('241',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['208','209','220','221','222','227','228','233','234','235','236','237','238','239','240','241','242','243'])).

thf('245',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['207','244'])).

thf('246',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['203','245'])).

thf('247',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['115'])).

thf('248',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['257'])).

thf('259',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['165','256','258'])).

thf('260',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['114','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','260'])).

thf('262',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','261'])).

thf('263',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['212','219'])).

thf('264',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('266',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('267',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('268',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('269',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('270',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['205'])).

thf('271',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('272',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['273'])).

thf('275',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['165','256','274'])).

thf('276',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['272','275'])).

thf('277',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['262','263','264','265','266','267','268','269','276','277','278','279'])).

thf('281',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','280'])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['154'])).

thf('284',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['165','256'])).

thf('285',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['283','284'])).

thf('286',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['282','285'])).

thf('287',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['290','291'])).

thf('293',plain,(
    $false ),
    inference(demod,[status(thm)],['0','292'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VmuPXsJTHp
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:08:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.82/9.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.82/9.00  % Solved by: fo/fo7.sh
% 8.82/9.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.82/9.00  % done 2808 iterations in 8.537s
% 8.82/9.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.82/9.00  % SZS output start Refutation
% 8.82/9.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.82/9.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.82/9.00  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 8.82/9.00  thf(sk_B_type, type, sk_B: $i).
% 8.82/9.00  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 8.82/9.00  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.82/9.00  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.82/9.00  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 8.82/9.00  thf(sk_A_type, type, sk_A: $i).
% 8.82/9.00  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 8.82/9.00  thf(sk_D_type, type, sk_D: $i).
% 8.82/9.00  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 8.82/9.00  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 8.82/9.00  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 8.82/9.00  thf(sk_E_type, type, sk_E: $i).
% 8.82/9.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.82/9.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.82/9.00  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.82/9.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.82/9.00  thf(sk_C_type, type, sk_C: $i).
% 8.82/9.00  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 8.82/9.00  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.82/9.00  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.82/9.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.82/9.00  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.82/9.00  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.82/9.00  thf(t132_tmap_1, conjecture,
% 8.82/9.00    (![A:$i]:
% 8.82/9.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.82/9.00       ( ![B:$i]:
% 8.82/9.00         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.82/9.00             ( l1_pre_topc @ B ) ) =>
% 8.82/9.00           ( ![C:$i]:
% 8.82/9.00             ( ( ( v1_funct_1 @ C ) & 
% 8.82/9.00                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                 ( m1_subset_1 @
% 8.82/9.00                   C @ 
% 8.82/9.00                   ( k1_zfmisc_1 @
% 8.82/9.00                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.82/9.00               ( ![D:$i]:
% 8.82/9.00                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 8.82/9.00                   ( ![E:$i]:
% 8.82/9.00                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 8.82/9.00                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 8.82/9.00                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 8.82/9.00                         ( ( ( v1_funct_1 @ C ) & 
% 8.82/9.00                             ( v1_funct_2 @
% 8.82/9.00                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                             ( v5_pre_topc @ C @ A @ B ) & 
% 8.82/9.00                             ( m1_subset_1 @
% 8.82/9.00                               C @ 
% 8.82/9.00                               ( k1_zfmisc_1 @
% 8.82/9.00                                 ( k2_zfmisc_1 @
% 8.82/9.00                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 8.82/9.00                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 8.82/9.00                             ( v1_funct_2 @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/9.00                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                             ( v5_pre_topc @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 8.82/9.00                             ( m1_subset_1 @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/9.00                               ( k1_zfmisc_1 @
% 8.82/9.00                                 ( k2_zfmisc_1 @
% 8.82/9.00                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.82/9.00                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 8.82/9.00                             ( v1_funct_2 @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 8.82/9.00                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                             ( v5_pre_topc @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 8.82/9.00                             ( m1_subset_1 @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 8.82/9.00                               ( k1_zfmisc_1 @
% 8.82/9.00                                 ( k2_zfmisc_1 @
% 8.82/9.00                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 8.82/9.00  thf(zf_stmt_0, negated_conjecture,
% 8.82/9.00    (~( ![A:$i]:
% 8.82/9.00        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 8.82/9.00            ( l1_pre_topc @ A ) ) =>
% 8.82/9.00          ( ![B:$i]:
% 8.82/9.00            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.82/9.00                ( l1_pre_topc @ B ) ) =>
% 8.82/9.00              ( ![C:$i]:
% 8.82/9.00                ( ( ( v1_funct_1 @ C ) & 
% 8.82/9.00                    ( v1_funct_2 @
% 8.82/9.00                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                    ( m1_subset_1 @
% 8.82/9.00                      C @ 
% 8.82/9.00                      ( k1_zfmisc_1 @
% 8.82/9.00                        ( k2_zfmisc_1 @
% 8.82/9.00                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.82/9.00                  ( ![D:$i]:
% 8.82/9.00                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 8.82/9.00                      ( ![E:$i]:
% 8.82/9.00                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 8.82/9.00                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 8.82/9.00                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 8.82/9.00                            ( ( ( v1_funct_1 @ C ) & 
% 8.82/9.00                                ( v1_funct_2 @
% 8.82/9.00                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                                ( v5_pre_topc @ C @ A @ B ) & 
% 8.82/9.00                                ( m1_subset_1 @
% 8.82/9.00                                  C @ 
% 8.82/9.00                                  ( k1_zfmisc_1 @
% 8.82/9.00                                    ( k2_zfmisc_1 @
% 8.82/9.00                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 8.82/9.00                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 8.82/9.00                                ( v1_funct_2 @
% 8.82/9.00                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/9.00                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                                ( v5_pre_topc @
% 8.82/9.00                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 8.82/9.00                                ( m1_subset_1 @
% 8.82/9.00                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/9.00                                  ( k1_zfmisc_1 @
% 8.82/9.00                                    ( k2_zfmisc_1 @
% 8.82/9.00                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.82/9.00                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 8.82/9.00                                ( v1_funct_2 @
% 8.82/9.00                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 8.82/9.00                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                                ( v5_pre_topc @
% 8.82/9.00                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 8.82/9.00                                ( m1_subset_1 @
% 8.82/9.00                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 8.82/9.00                                  ( k1_zfmisc_1 @
% 8.82/9.00                                    ( k2_zfmisc_1 @
% 8.82/9.00                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 8.82/9.00    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 8.82/9.00  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf(dt_k1_tsep_1, axiom,
% 8.82/9.00    (![A:$i,B:$i,C:$i]:
% 8.82/9.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 8.82/9.00         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 8.82/9.00         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 8.82/9.00       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 8.82/9.00         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 8.82/9.00         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 8.82/9.00  thf('3', plain,
% 8.82/9.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.82/9.00         (~ (m1_pre_topc @ X19 @ X20)
% 8.82/9.00          | (v2_struct_0 @ X19)
% 8.82/9.00          | ~ (l1_pre_topc @ X20)
% 8.82/9.00          | (v2_struct_0 @ X20)
% 8.82/9.00          | (v2_struct_0 @ X21)
% 8.82/9.00          | ~ (m1_pre_topc @ X21 @ X20)
% 8.82/9.00          | (m1_pre_topc @ (k1_tsep_1 @ X20 @ X19 @ X21) @ X20))),
% 8.82/9.00      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 8.82/9.00  thf('4', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 8.82/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ X0)
% 8.82/9.00          | (v2_struct_0 @ sk_A)
% 8.82/9.00          | ~ (l1_pre_topc @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ sk_D))),
% 8.82/9.00      inference('sup-', [status(thm)], ['2', '3'])).
% 8.82/9.00  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('6', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 8.82/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ X0)
% 8.82/9.00          | (v2_struct_0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ sk_D))),
% 8.82/9.00      inference('demod', [status(thm)], ['4', '5'])).
% 8.82/9.00  thf('7', plain,
% 8.82/9.00      (((v2_struct_0 @ sk_D)
% 8.82/9.00        | (v2_struct_0 @ sk_A)
% 8.82/9.00        | (v2_struct_0 @ sk_E)
% 8.82/9.00        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_A))),
% 8.82/9.00      inference('sup-', [status(thm)], ['1', '6'])).
% 8.82/9.00  thf('8', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('9', plain,
% 8.82/9.00      (((v2_struct_0 @ sk_D)
% 8.82/9.00        | (v2_struct_0 @ sk_A)
% 8.82/9.00        | (v2_struct_0 @ sk_E)
% 8.82/9.00        | (m1_pre_topc @ sk_A @ sk_A))),
% 8.82/9.00      inference('demod', [status(thm)], ['7', '8'])).
% 8.82/9.00  thf('10', plain,
% 8.82/9.00      ((m1_subset_1 @ sk_C @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf(d4_tmap_1, axiom,
% 8.82/9.00    (![A:$i]:
% 8.82/9.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.82/9.00       ( ![B:$i]:
% 8.82/9.00         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.82/9.00             ( l1_pre_topc @ B ) ) =>
% 8.82/9.00           ( ![C:$i]:
% 8.82/9.00             ( ( ( v1_funct_1 @ C ) & 
% 8.82/9.00                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                 ( m1_subset_1 @
% 8.82/9.00                   C @ 
% 8.82/9.00                   ( k1_zfmisc_1 @
% 8.82/9.00                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.82/9.00               ( ![D:$i]:
% 8.82/9.00                 ( ( m1_pre_topc @ D @ A ) =>
% 8.82/9.00                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 8.82/9.00                     ( k2_partfun1 @
% 8.82/9.00                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 8.82/9.00                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 8.82/9.00  thf('11', plain,
% 8.82/9.00      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 8.82/9.00         ((v2_struct_0 @ X15)
% 8.82/9.00          | ~ (v2_pre_topc @ X15)
% 8.82/9.00          | ~ (l1_pre_topc @ X15)
% 8.82/9.00          | ~ (m1_pre_topc @ X16 @ X17)
% 8.82/9.00          | ((k2_tmap_1 @ X17 @ X15 @ X18 @ X16)
% 8.82/9.00              = (k2_partfun1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ 
% 8.82/9.00                 X18 @ (u1_struct_0 @ X16)))
% 8.82/9.00          | ~ (m1_subset_1 @ X18 @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))))
% 8.82/9.00          | ~ (v1_funct_2 @ X18 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15))
% 8.82/9.00          | ~ (v1_funct_1 @ X18)
% 8.82/9.00          | ~ (l1_pre_topc @ X17)
% 8.82/9.00          | ~ (v2_pre_topc @ X17)
% 8.82/9.00          | (v2_struct_0 @ X17))),
% 8.82/9.00      inference('cnf', [status(esa)], [d4_tmap_1])).
% 8.82/9.00  thf('12', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v2_struct_0 @ sk_A)
% 8.82/9.00          | ~ (v2_pre_topc @ sk_A)
% 8.82/9.00          | ~ (l1_pre_topc @ sk_A)
% 8.82/9.00          | ~ (v1_funct_1 @ sk_C)
% 8.82/9.00          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 8.82/9.00              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.82/9.00                 sk_C @ (u1_struct_0 @ X0)))
% 8.82/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/9.00          | ~ (l1_pre_topc @ sk_B)
% 8.82/9.00          | ~ (v2_pre_topc @ sk_B)
% 8.82/9.00          | (v2_struct_0 @ sk_B))),
% 8.82/9.00      inference('sup-', [status(thm)], ['10', '11'])).
% 8.82/9.00  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('16', plain,
% 8.82/9.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('17', plain,
% 8.82/9.00      ((m1_subset_1 @ sk_C @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf(redefinition_k2_partfun1, axiom,
% 8.82/9.00    (![A:$i,B:$i,C:$i,D:$i]:
% 8.82/9.00     ( ( ( v1_funct_1 @ C ) & 
% 8.82/9.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.82/9.00       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 8.82/9.00  thf('18', plain,
% 8.82/9.00      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 8.82/9.00         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 8.82/9.00          | ~ (v1_funct_1 @ X8)
% 8.82/9.00          | ((k2_partfun1 @ X9 @ X10 @ X8 @ X11) = (k7_relat_1 @ X8 @ X11)))),
% 8.82/9.00      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 8.82/9.00  thf('19', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 8.82/9.00            X0) = (k7_relat_1 @ sk_C @ X0))
% 8.82/9.00          | ~ (v1_funct_1 @ sk_C))),
% 8.82/9.00      inference('sup-', [status(thm)], ['17', '18'])).
% 8.82/9.00  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('21', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 8.82/9.00           X0) = (k7_relat_1 @ sk_C @ X0))),
% 8.82/9.00      inference('demod', [status(thm)], ['19', '20'])).
% 8.82/9.00  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('24', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v2_struct_0 @ sk_A)
% 8.82/9.00          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 8.82/9.00              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 8.82/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ sk_B))),
% 8.82/9.00      inference('demod', [status(thm)],
% 8.82/9.00                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 8.82/9.00  thf('25', plain,
% 8.82/9.00      (((v2_struct_0 @ sk_E)
% 8.82/9.00        | (v2_struct_0 @ sk_A)
% 8.82/9.00        | (v2_struct_0 @ sk_D)
% 8.82/9.00        | (v2_struct_0 @ sk_B)
% 8.82/9.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 8.82/9.00            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 8.82/9.00        | (v2_struct_0 @ sk_A))),
% 8.82/9.00      inference('sup-', [status(thm)], ['9', '24'])).
% 8.82/9.00  thf('26', plain,
% 8.82/9.00      ((m1_subset_1 @ sk_C @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf(cc2_relset_1, axiom,
% 8.82/9.00    (![A:$i,B:$i,C:$i]:
% 8.82/9.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.82/9.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.82/9.00  thf('27', plain,
% 8.82/9.00      (![X5 : $i, X6 : $i, X7 : $i]:
% 8.82/9.00         ((v4_relat_1 @ X5 @ X6)
% 8.82/9.00          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 8.82/9.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.82/9.00  thf('28', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 8.82/9.00      inference('sup-', [status(thm)], ['26', '27'])).
% 8.82/9.00  thf(t209_relat_1, axiom,
% 8.82/9.00    (![A:$i,B:$i]:
% 8.82/9.00     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 8.82/9.00       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 8.82/9.00  thf('29', plain,
% 8.82/9.00      (![X0 : $i, X1 : $i]:
% 8.82/9.00         (((X0) = (k7_relat_1 @ X0 @ X1))
% 8.82/9.00          | ~ (v4_relat_1 @ X0 @ X1)
% 8.82/9.00          | ~ (v1_relat_1 @ X0))),
% 8.82/9.00      inference('cnf', [status(esa)], [t209_relat_1])).
% 8.82/9.00  thf('30', plain,
% 8.82/9.00      ((~ (v1_relat_1 @ sk_C)
% 8.82/9.00        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 8.82/9.00      inference('sup-', [status(thm)], ['28', '29'])).
% 8.82/9.00  thf('31', plain,
% 8.82/9.00      ((m1_subset_1 @ sk_C @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf(cc1_relset_1, axiom,
% 8.82/9.00    (![A:$i,B:$i,C:$i]:
% 8.82/9.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.82/9.00       ( v1_relat_1 @ C ) ))).
% 8.82/9.00  thf('32', plain,
% 8.82/9.00      (![X2 : $i, X3 : $i, X4 : $i]:
% 8.82/9.00         ((v1_relat_1 @ X2)
% 8.82/9.00          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 8.82/9.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.82/9.00  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 8.82/9.00      inference('sup-', [status(thm)], ['31', '32'])).
% 8.82/9.00  thf('34', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 8.82/9.00      inference('demod', [status(thm)], ['30', '33'])).
% 8.82/9.00  thf('35', plain,
% 8.82/9.00      (((v2_struct_0 @ sk_E)
% 8.82/9.00        | (v2_struct_0 @ sk_A)
% 8.82/9.00        | (v2_struct_0 @ sk_D)
% 8.82/9.00        | (v2_struct_0 @ sk_B)
% 8.82/9.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 8.82/9.00        | (v2_struct_0 @ sk_A))),
% 8.82/9.00      inference('demod', [status(thm)], ['25', '34'])).
% 8.82/9.00  thf('36', plain,
% 8.82/9.00      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 8.82/9.00        | (v2_struct_0 @ sk_B)
% 8.82/9.00        | (v2_struct_0 @ sk_D)
% 8.82/9.00        | (v2_struct_0 @ sk_A)
% 8.82/9.00        | (v2_struct_0 @ sk_E))),
% 8.82/9.00      inference('simplify', [status(thm)], ['35'])).
% 8.82/9.00  thf('37', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('38', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v2_struct_0 @ sk_A)
% 8.82/9.00          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 8.82/9.00              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 8.82/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ sk_B))),
% 8.82/9.00      inference('demod', [status(thm)],
% 8.82/9.00                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 8.82/9.00  thf('39', plain,
% 8.82/9.00      (((v2_struct_0 @ sk_B)
% 8.82/9.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/9.00            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 8.82/9.00        | (v2_struct_0 @ sk_A))),
% 8.82/9.00      inference('sup-', [status(thm)], ['37', '38'])).
% 8.82/9.00  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('41', plain,
% 8.82/9.00      (((v2_struct_0 @ sk_A)
% 8.82/9.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/9.00            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))),
% 8.82/9.00      inference('clc', [status(thm)], ['39', '40'])).
% 8.82/9.00  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('43', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.82/9.00  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('45', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v2_struct_0 @ sk_A)
% 8.82/9.00          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 8.82/9.00              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 8.82/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ sk_B))),
% 8.82/9.00      inference('demod', [status(thm)],
% 8.82/9.00                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 8.82/9.00  thf('46', plain,
% 8.82/9.00      (((v2_struct_0 @ sk_B)
% 8.82/9.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 8.82/9.00        | (v2_struct_0 @ sk_A))),
% 8.82/9.00      inference('sup-', [status(thm)], ['44', '45'])).
% 8.82/9.00  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('48', plain,
% 8.82/9.00      (((v2_struct_0 @ sk_A)
% 8.82/9.00        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))),
% 8.82/9.00      inference('clc', [status(thm)], ['46', '47'])).
% 8.82/9.00  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('50', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/9.00  thf(t129_tmap_1, axiom,
% 8.82/9.00    (![A:$i]:
% 8.82/9.00     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.82/9.00       ( ![B:$i]:
% 8.82/9.00         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.82/9.00             ( l1_pre_topc @ B ) ) =>
% 8.82/9.00           ( ![C:$i]:
% 8.82/9.00             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 8.82/9.00               ( ![D:$i]:
% 8.82/9.00                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 8.82/9.00                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 8.82/9.00                     ( ![E:$i]:
% 8.82/9.00                       ( ( ( v1_funct_1 @ E ) & 
% 8.82/9.00                           ( v1_funct_2 @
% 8.82/9.00                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                           ( m1_subset_1 @
% 8.82/9.00                             E @ 
% 8.82/9.00                             ( k1_zfmisc_1 @
% 8.82/9.00                               ( k2_zfmisc_1 @
% 8.82/9.00                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.82/9.00                         ( ( ( v1_funct_1 @
% 8.82/9.00                               ( k2_tmap_1 @
% 8.82/9.00                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 8.82/9.00                             ( v1_funct_2 @
% 8.82/9.00                               ( k2_tmap_1 @
% 8.82/9.00                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/9.00                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/9.00                               ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                             ( v5_pre_topc @
% 8.82/9.00                               ( k2_tmap_1 @
% 8.82/9.00                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/9.00                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 8.82/9.00                             ( m1_subset_1 @
% 8.82/9.00                               ( k2_tmap_1 @
% 8.82/9.00                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/9.00                               ( k1_zfmisc_1 @
% 8.82/9.00                                 ( k2_zfmisc_1 @
% 8.82/9.00                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/9.00                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 8.82/9.00                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 8.82/9.00                             ( v1_funct_2 @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 8.82/9.00                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                             ( v5_pre_topc @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 8.82/9.00                             ( m1_subset_1 @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 8.82/9.00                               ( k1_zfmisc_1 @
% 8.82/9.00                                 ( k2_zfmisc_1 @
% 8.82/9.00                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.82/9.00                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 8.82/9.00                             ( v1_funct_2 @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 8.82/9.00                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00                             ( v5_pre_topc @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 8.82/9.00                             ( m1_subset_1 @
% 8.82/9.00                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 8.82/9.00                               ( k1_zfmisc_1 @
% 8.82/9.00                                 ( k2_zfmisc_1 @
% 8.82/9.00                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 8.82/9.00  thf('51', plain,
% 8.82/9.00      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.82/9.00         ((v2_struct_0 @ X26)
% 8.82/9.00          | ~ (v2_pre_topc @ X26)
% 8.82/9.00          | ~ (l1_pre_topc @ X26)
% 8.82/9.00          | (v2_struct_0 @ X27)
% 8.82/9.00          | ~ (m1_pre_topc @ X27 @ X28)
% 8.82/9.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X30))
% 8.82/9.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X30) @ 
% 8.82/9.00               (u1_struct_0 @ X30) @ (u1_struct_0 @ X26))
% 8.82/9.00          | ~ (v5_pre_topc @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X30) @ X30 @ X26)
% 8.82/9.00          | ~ (m1_subset_1 @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X30) @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X26))))
% 8.82/9.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X27))
% 8.82/9.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X27) @ 
% 8.82/9.00               (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 8.82/9.00          | ~ (v5_pre_topc @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X27) @ X27 @ X26)
% 8.82/9.00          | ~ (m1_subset_1 @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X27) @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 8.82/9.00          | (v5_pre_topc @ 
% 8.82/9.00             (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.82/9.00             (k1_tsep_1 @ X28 @ X30 @ X27) @ X26)
% 8.82/9.00          | ~ (m1_subset_1 @ X29 @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 8.82/9.00          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 8.82/9.00          | ~ (v1_funct_1 @ X29)
% 8.82/9.00          | ~ (r4_tsep_1 @ X28 @ X30 @ X27)
% 8.82/9.00          | ~ (m1_pre_topc @ X30 @ X28)
% 8.82/9.00          | (v2_struct_0 @ X30)
% 8.82/9.00          | ~ (l1_pre_topc @ X28)
% 8.82/9.00          | ~ (v2_pre_topc @ X28)
% 8.82/9.00          | (v2_struct_0 @ X28))),
% 8.82/9.00      inference('cnf', [status(esa)], [t129_tmap_1])).
% 8.82/9.00  thf('52', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         (~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/9.00             (k1_zfmisc_1 @ 
% 8.82/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00          | (v2_struct_0 @ sk_A)
% 8.82/9.00          | ~ (v2_pre_topc @ sk_A)
% 8.82/9.00          | ~ (l1_pre_topc @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ sk_D)
% 8.82/9.00          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 8.82/9.00          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 8.82/9.00          | ~ (v1_funct_1 @ sk_C)
% 8.82/9.00          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ~ (m1_subset_1 @ sk_C @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00          | (v5_pre_topc @ 
% 8.82/9.00             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 8.82/9.00             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 8.82/9.00          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.82/9.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/9.00          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.82/9.00               sk_B)
% 8.82/9.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.82/9.00               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 8.82/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ X0)
% 8.82/9.00          | ~ (l1_pre_topc @ sk_B)
% 8.82/9.00          | ~ (v2_pre_topc @ sk_B)
% 8.82/9.00          | (v2_struct_0 @ sk_B))),
% 8.82/9.00      inference('sup-', [status(thm)], ['50', '51'])).
% 8.82/9.00  thf('53', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/9.00  thf('54', plain,
% 8.82/9.00      ((m1_subset_1 @ sk_C @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf(dt_k2_tmap_1, axiom,
% 8.82/9.00    (![A:$i,B:$i,C:$i,D:$i]:
% 8.82/9.00     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 8.82/9.00         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/9.00         ( m1_subset_1 @
% 8.82/9.00           C @ 
% 8.82/9.00           ( k1_zfmisc_1 @
% 8.82/9.00             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.82/9.00         ( l1_struct_0 @ D ) ) =>
% 8.82/9.00       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 8.82/9.00         ( v1_funct_2 @
% 8.82/9.00           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 8.82/9.00           ( u1_struct_0 @ B ) ) & 
% 8.82/9.00         ( m1_subset_1 @
% 8.82/9.00           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/9.00           ( k1_zfmisc_1 @
% 8.82/9.00             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 8.82/9.00  thf('55', plain,
% 8.82/9.00      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 8.82/9.00         (~ (m1_subset_1 @ X22 @ 
% 8.82/9.00             (k1_zfmisc_1 @ 
% 8.82/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))))
% 8.82/9.00          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 8.82/9.00          | ~ (v1_funct_1 @ X22)
% 8.82/9.00          | ~ (l1_struct_0 @ X24)
% 8.82/9.00          | ~ (l1_struct_0 @ X23)
% 8.82/9.00          | ~ (l1_struct_0 @ X25)
% 8.82/9.00          | (m1_subset_1 @ (k2_tmap_1 @ X23 @ X24 @ X22 @ X25) @ 
% 8.82/9.00             (k1_zfmisc_1 @ 
% 8.82/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24)))))),
% 8.82/9.00      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 8.82/9.00  thf('56', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00           (k1_zfmisc_1 @ 
% 8.82/9.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00          | ~ (l1_struct_0 @ X0)
% 8.82/9.00          | ~ (l1_struct_0 @ sk_A)
% 8.82/9.00          | ~ (l1_struct_0 @ sk_B)
% 8.82/9.00          | ~ (v1_funct_1 @ sk_C)
% 8.82/9.00          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 8.82/9.00      inference('sup-', [status(thm)], ['54', '55'])).
% 8.82/9.00  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf(dt_l1_pre_topc, axiom,
% 8.82/9.00    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 8.82/9.00  thf('58', plain,
% 8.82/9.00      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 8.82/9.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.82/9.00  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 8.82/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.82/9.00  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('61', plain,
% 8.82/9.00      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 8.82/9.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.82/9.00  thf('62', plain, ((l1_struct_0 @ sk_B)),
% 8.82/9.00      inference('sup-', [status(thm)], ['60', '61'])).
% 8.82/9.00  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('64', plain,
% 8.82/9.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('65', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00           (k1_zfmisc_1 @ 
% 8.82/9.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00          | ~ (l1_struct_0 @ X0))),
% 8.82/9.00      inference('demod', [status(thm)], ['56', '59', '62', '63', '64'])).
% 8.82/9.00  thf('66', plain,
% 8.82/9.00      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/9.00         (k1_zfmisc_1 @ 
% 8.82/9.00          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00        | ~ (l1_struct_0 @ sk_D))),
% 8.82/9.00      inference('sup+', [status(thm)], ['53', '65'])).
% 8.82/9.00  thf('67', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf(dt_m1_pre_topc, axiom,
% 8.82/9.00    (![A:$i]:
% 8.82/9.00     ( ( l1_pre_topc @ A ) =>
% 8.82/9.00       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 8.82/9.00  thf('68', plain,
% 8.82/9.00      (![X13 : $i, X14 : $i]:
% 8.82/9.00         (~ (m1_pre_topc @ X13 @ X14)
% 8.82/9.00          | (l1_pre_topc @ X13)
% 8.82/9.00          | ~ (l1_pre_topc @ X14))),
% 8.82/9.00      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 8.82/9.00  thf('69', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 8.82/9.00      inference('sup-', [status(thm)], ['67', '68'])).
% 8.82/9.00  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('71', plain, ((l1_pre_topc @ sk_D)),
% 8.82/9.00      inference('demod', [status(thm)], ['69', '70'])).
% 8.82/9.00  thf('72', plain,
% 8.82/9.00      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 8.82/9.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.82/9.00  thf('73', plain, ((l1_struct_0 @ sk_D)),
% 8.82/9.00      inference('sup-', [status(thm)], ['71', '72'])).
% 8.82/9.00  thf('74', plain,
% 8.82/9.00      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('demod', [status(thm)], ['66', '73'])).
% 8.82/9.00  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('77', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('79', plain,
% 8.82/9.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('80', plain,
% 8.82/9.00      ((m1_subset_1 @ sk_C @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('81', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/9.00  thf('82', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/9.00  thf('83', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/9.00  thf('84', plain,
% 8.82/9.00      ((m1_subset_1 @ sk_C @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('85', plain,
% 8.82/9.00      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 8.82/9.00         (~ (m1_subset_1 @ X22 @ 
% 8.82/9.00             (k1_zfmisc_1 @ 
% 8.82/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))))
% 8.82/9.00          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 8.82/9.00          | ~ (v1_funct_1 @ X22)
% 8.82/9.00          | ~ (l1_struct_0 @ X24)
% 8.82/9.00          | ~ (l1_struct_0 @ X23)
% 8.82/9.00          | ~ (l1_struct_0 @ X25)
% 8.82/9.00          | (v1_funct_2 @ (k2_tmap_1 @ X23 @ X24 @ X22 @ X25) @ 
% 8.82/9.00             (u1_struct_0 @ X25) @ (u1_struct_0 @ X24)))),
% 8.82/9.00      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 8.82/9.00  thf('86', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ~ (l1_struct_0 @ X0)
% 8.82/9.00          | ~ (l1_struct_0 @ sk_A)
% 8.82/9.00          | ~ (l1_struct_0 @ sk_B)
% 8.82/9.00          | ~ (v1_funct_1 @ sk_C)
% 8.82/9.00          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 8.82/9.00      inference('sup-', [status(thm)], ['84', '85'])).
% 8.82/9.00  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 8.82/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.82/9.00  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 8.82/9.00      inference('sup-', [status(thm)], ['60', '61'])).
% 8.82/9.00  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('90', plain,
% 8.82/9.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('91', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ~ (l1_struct_0 @ X0))),
% 8.82/9.00      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 8.82/9.00  thf('92', plain,
% 8.82/9.00      (((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/9.00         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 8.82/9.00        | ~ (l1_struct_0 @ sk_D))),
% 8.82/9.00      inference('sup+', [status(thm)], ['83', '91'])).
% 8.82/9.00  thf('93', plain, ((l1_struct_0 @ sk_D)),
% 8.82/9.00      inference('sup-', [status(thm)], ['71', '72'])).
% 8.82/9.00  thf('94', plain,
% 8.82/9.00      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/9.00        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 8.82/9.00      inference('demod', [status(thm)], ['92', '93'])).
% 8.82/9.00  thf('95', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/9.00  thf('96', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/9.00  thf('97', plain,
% 8.82/9.00      ((m1_subset_1 @ sk_C @ 
% 8.82/9.00        (k1_zfmisc_1 @ 
% 8.82/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('98', plain,
% 8.82/9.00      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 8.82/9.00         (~ (m1_subset_1 @ X22 @ 
% 8.82/9.00             (k1_zfmisc_1 @ 
% 8.82/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))))
% 8.82/9.00          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 8.82/9.00          | ~ (v1_funct_1 @ X22)
% 8.82/9.00          | ~ (l1_struct_0 @ X24)
% 8.82/9.00          | ~ (l1_struct_0 @ X23)
% 8.82/9.00          | ~ (l1_struct_0 @ X25)
% 8.82/9.00          | (v1_funct_1 @ (k2_tmap_1 @ X23 @ X24 @ X22 @ X25)))),
% 8.82/9.00      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 8.82/9.00  thf('99', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/9.00          | ~ (l1_struct_0 @ X0)
% 8.82/9.00          | ~ (l1_struct_0 @ sk_A)
% 8.82/9.00          | ~ (l1_struct_0 @ sk_B)
% 8.82/9.00          | ~ (v1_funct_1 @ sk_C)
% 8.82/9.00          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 8.82/9.00      inference('sup-', [status(thm)], ['97', '98'])).
% 8.82/9.00  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 8.82/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.82/9.00  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 8.82/9.00      inference('sup-', [status(thm)], ['60', '61'])).
% 8.82/9.00  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('103', plain,
% 8.82/9.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('104', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/9.00          | ~ (l1_struct_0 @ X0))),
% 8.82/9.00      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 8.82/9.00  thf('105', plain,
% 8.82/9.00      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 8.82/9.00        | ~ (l1_struct_0 @ sk_D))),
% 8.82/9.00      inference('sup+', [status(thm)], ['96', '104'])).
% 8.82/9.00  thf('106', plain, ((l1_struct_0 @ sk_D)),
% 8.82/9.00      inference('sup-', [status(thm)], ['71', '72'])).
% 8.82/9.00  thf('107', plain,
% 8.82/9.00      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('demod', [status(thm)], ['105', '106'])).
% 8.82/9.00  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('109', plain, ((v2_pre_topc @ sk_B)),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('110', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v2_struct_0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ sk_D)
% 8.82/9.00          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 8.82/9.00          | (v5_pre_topc @ 
% 8.82/9.00             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 8.82/9.00             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 8.82/9.00          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.82/9.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/9.00          | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/9.00               sk_D @ sk_B)
% 8.82/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ X0)
% 8.82/9.00          | (v2_struct_0 @ sk_B))),
% 8.82/9.00      inference('demod', [status(thm)],
% 8.82/9.00                ['52', '74', '75', '76', '77', '78', '79', '80', '81', '82', 
% 8.82/9.00                 '94', '95', '107', '108', '109'])).
% 8.82/9.00  thf('111', plain,
% 8.82/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 8.82/9.00        | (v1_funct_1 @ sk_C))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('112', plain,
% 8.82/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 8.82/9.00         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.82/9.00               sk_B)))),
% 8.82/9.00      inference('split', [status(esa)], ['111'])).
% 8.82/9.00  thf('113', plain,
% 8.82/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/9.00  thf('114', plain,
% 8.82/9.00      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B))
% 8.82/9.00         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.82/9.00               sk_B)))),
% 8.82/9.00      inference('demod', [status(thm)], ['112', '113'])).
% 8.82/9.00  thf('115', plain,
% 8.82/9.00      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 8.82/9.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('116', plain,
% 8.82/9.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 8.82/9.00         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/9.00      inference('split', [status(esa)], ['115'])).
% 8.82/9.00  thf('117', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/9.00          | ~ (l1_struct_0 @ X0))),
% 8.82/9.00      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 8.82/9.00  thf('118', plain,
% 8.82/9.00      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 8.82/9.00        | (v2_struct_0 @ sk_B)
% 8.82/9.00        | (v2_struct_0 @ sk_D)
% 8.82/9.00        | (v2_struct_0 @ sk_A)
% 8.82/9.00        | (v2_struct_0 @ sk_E))),
% 8.82/9.00      inference('simplify', [status(thm)], ['35'])).
% 8.82/9.00  thf('119', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ~ (l1_struct_0 @ X0))),
% 8.82/9.00      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 8.82/9.00  thf('120', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/9.00  thf('121', plain,
% 8.82/9.00      (![X0 : $i]:
% 8.82/9.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/9.00           (k1_zfmisc_1 @ 
% 8.82/9.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00          | ~ (l1_struct_0 @ X0))),
% 8.82/9.00      inference('demod', [status(thm)], ['56', '59', '62', '63', '64'])).
% 8.82/9.00  thf('122', plain,
% 8.82/9.00      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.82/9.00         ((v2_struct_0 @ X26)
% 8.82/9.00          | ~ (v2_pre_topc @ X26)
% 8.82/9.00          | ~ (l1_pre_topc @ X26)
% 8.82/9.00          | (v2_struct_0 @ X27)
% 8.82/9.00          | ~ (m1_pre_topc @ X27 @ X28)
% 8.82/9.00          | ~ (v1_funct_1 @ 
% 8.82/9.00               (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)))
% 8.82/9.00          | ~ (v1_funct_2 @ 
% 8.82/9.00               (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.82/9.00               (u1_struct_0 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.82/9.00               (u1_struct_0 @ X26))
% 8.82/9.00          | ~ (v5_pre_topc @ 
% 8.82/9.00               (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.82/9.00               (k1_tsep_1 @ X28 @ X30 @ X27) @ X26)
% 8.82/9.00          | ~ (m1_subset_1 @ 
% 8.82/9.00               (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.82/9.00                 (u1_struct_0 @ X26))))
% 8.82/9.00          | (v5_pre_topc @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X27) @ X27 @ X26)
% 8.82/9.00          | ~ (m1_subset_1 @ X29 @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 8.82/9.00          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 8.82/9.00          | ~ (v1_funct_1 @ X29)
% 8.82/9.00          | ~ (r4_tsep_1 @ X28 @ X30 @ X27)
% 8.82/9.00          | ~ (m1_pre_topc @ X30 @ X28)
% 8.82/9.00          | (v2_struct_0 @ X30)
% 8.82/9.00          | ~ (l1_pre_topc @ X28)
% 8.82/9.00          | ~ (v2_pre_topc @ X28)
% 8.82/9.00          | (v2_struct_0 @ X28))),
% 8.82/9.00      inference('cnf', [status(esa)], [t129_tmap_1])).
% 8.82/9.00  thf('123', plain,
% 8.82/9.00      (![X0 : $i, X1 : $i]:
% 8.82/9.00         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 8.82/9.00          | (v2_struct_0 @ sk_A)
% 8.82/9.00          | ~ (v2_pre_topc @ sk_A)
% 8.82/9.00          | ~ (l1_pre_topc @ sk_A)
% 8.82/9.00          | (v2_struct_0 @ X1)
% 8.82/9.00          | ~ (m1_pre_topc @ X1 @ sk_A)
% 8.82/9.00          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 8.82/9.00          | ~ (v1_funct_1 @ sk_C)
% 8.82/9.00          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/9.00          | ~ (m1_subset_1 @ sk_C @ 
% 8.82/9.00               (k1_zfmisc_1 @ 
% 8.82/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.82/9.00          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.82/9.00          | ~ (v5_pre_topc @ 
% 8.82/9.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.82/9.00               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 8.85/9.00          | ~ (v1_funct_2 @ 
% 8.85/9.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.85/9.00               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.85/9.00               (u1_struct_0 @ sk_B))
% 8.85/9.00          | ~ (v1_funct_1 @ 
% 8.85/9.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 8.85/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.85/9.00          | (v2_struct_0 @ X0)
% 8.85/9.00          | ~ (l1_pre_topc @ sk_B)
% 8.85/9.00          | ~ (v2_pre_topc @ sk_B)
% 8.85/9.00          | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('sup-', [status(thm)], ['121', '122'])).
% 8.85/9.00  thf('124', plain, ((v2_pre_topc @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('125', plain, ((l1_pre_topc @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('127', plain,
% 8.85/9.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('128', plain,
% 8.85/9.00      ((m1_subset_1 @ sk_C @ 
% 8.85/9.00        (k1_zfmisc_1 @ 
% 8.85/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('129', plain, ((l1_pre_topc @ sk_B)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('130', plain, ((v2_pre_topc @ sk_B)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('131', plain,
% 8.85/9.00      (![X0 : $i, X1 : $i]:
% 8.85/9.00         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 8.85/9.00          | (v2_struct_0 @ sk_A)
% 8.85/9.00          | (v2_struct_0 @ X1)
% 8.85/9.00          | ~ (m1_pre_topc @ X1 @ sk_A)
% 8.85/9.00          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 8.85/9.00          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.85/9.00          | ~ (v5_pre_topc @ 
% 8.85/9.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.85/9.00               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 8.85/9.00          | ~ (v1_funct_2 @ 
% 8.85/9.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.85/9.00               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.85/9.00               (u1_struct_0 @ sk_B))
% 8.85/9.00          | ~ (v1_funct_1 @ 
% 8.85/9.00               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 8.85/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.85/9.00          | (v2_struct_0 @ X0)
% 8.85/9.00          | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('demod', [status(thm)],
% 8.85/9.00                ['123', '124', '125', '126', '127', '128', '129', '130'])).
% 8.85/9.00  thf('132', plain,
% 8.85/9.00      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 8.85/9.00           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.85/9.00           (u1_struct_0 @ sk_B))
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 8.85/9.00        | ~ (v1_funct_1 @ 
% 8.85/9.00             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 8.85/9.00        | ~ (v5_pre_topc @ 
% 8.85/9.00             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.85/9.00             (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 8.85/9.00        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 8.85/9.00        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 8.85/9.00        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['120', '131'])).
% 8.85/9.00  thf('133', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('134', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('135', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('136', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('137', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('138', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('139', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('140', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('141', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('142', plain, ((l1_struct_0 @ sk_A)),
% 8.85/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.85/9.00  thf('143', plain,
% 8.85/9.00      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 8.85/9.00           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A))),
% 8.85/9.00      inference('demod', [status(thm)],
% 8.85/9.00                ['132', '133', '134', '135', '136', '137', '138', '139', 
% 8.85/9.00                 '140', '141', '142'])).
% 8.85/9.00  thf('144', plain,
% 8.85/9.00      ((~ (l1_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('sup-', [status(thm)], ['119', '143'])).
% 8.85/9.00  thf('145', plain, ((l1_struct_0 @ sk_A)),
% 8.85/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.85/9.00  thf('146', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('demod', [status(thm)], ['144', '145'])).
% 8.85/9.00  thf('147', plain,
% 8.85/9.00      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A))),
% 8.85/9.00      inference('sup-', [status(thm)], ['118', '146'])).
% 8.85/9.00  thf('148', plain,
% 8.85/9.00      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('simplify', [status(thm)], ['147'])).
% 8.85/9.00  thf('149', plain,
% 8.85/9.00      ((~ (l1_struct_0 @ sk_A)
% 8.85/9.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00           sk_B))),
% 8.85/9.00      inference('sup-', [status(thm)], ['117', '148'])).
% 8.85/9.00  thf('150', plain, ((l1_struct_0 @ sk_A)),
% 8.85/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.85/9.00  thf('151', plain,
% 8.85/9.00      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00           sk_B))),
% 8.85/9.00      inference('demod', [status(thm)], ['149', '150'])).
% 8.85/9.00  thf('152', plain,
% 8.85/9.00      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00          sk_B)
% 8.85/9.00         | (v2_struct_0 @ sk_B)
% 8.85/9.00         | (v2_struct_0 @ sk_D)
% 8.85/9.00         | (v2_struct_0 @ sk_A)
% 8.85/9.00         | (v2_struct_0 @ sk_E))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['116', '151'])).
% 8.85/9.00  thf('153', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('154', plain,
% 8.85/9.00      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.85/9.00           (k1_zfmisc_1 @ 
% 8.85/9.00            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.85/9.00             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 8.85/9.00        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.85/9.00             (k1_zfmisc_1 @ 
% 8.85/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.85/9.00             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 8.85/9.00        | ~ (m1_subset_1 @ sk_C @ 
% 8.85/9.00             (k1_zfmisc_1 @ 
% 8.85/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v1_funct_1 @ sk_C))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('155', plain,
% 8.85/9.00      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 8.85/9.00         <= (~
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('split', [status(esa)], ['154'])).
% 8.85/9.00  thf('156', plain,
% 8.85/9.00      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00           sk_B))
% 8.85/9.00         <= (~
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['153', '155'])).
% 8.85/9.00  thf('157', plain,
% 8.85/9.00      ((((v2_struct_0 @ sk_E)
% 8.85/9.00         | (v2_struct_0 @ sk_A)
% 8.85/9.00         | (v2_struct_0 @ sk_D)
% 8.85/9.00         | (v2_struct_0 @ sk_B)))
% 8.85/9.00         <= (~
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['152', '156'])).
% 8.85/9.00  thf('158', plain, (~ (v2_struct_0 @ sk_B)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('159', plain,
% 8.85/9.00      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 8.85/9.00         <= (~
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['157', '158'])).
% 8.85/9.00  thf('160', plain, (~ (v2_struct_0 @ sk_D)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('161', plain,
% 8.85/9.00      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 8.85/9.00         <= (~
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('clc', [status(thm)], ['159', '160'])).
% 8.85/9.00  thf('162', plain, (~ (v2_struct_0 @ sk_E)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('163', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_A))
% 8.85/9.00         <= (~
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('clc', [status(thm)], ['161', '162'])).
% 8.85/9.00  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('165', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 8.85/9.00       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('sup-', [status(thm)], ['163', '164'])).
% 8.85/9.00  thf('166', plain,
% 8.85/9.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 8.85/9.00         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('split', [status(esa)], ['115'])).
% 8.85/9.00  thf('167', plain,
% 8.85/9.00      (![X0 : $i]:
% 8.85/9.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.85/9.00          | ~ (l1_struct_0 @ X0))),
% 8.85/9.00      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 8.85/9.00  thf('168', plain,
% 8.85/9.00      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_E))),
% 8.85/9.00      inference('simplify', [status(thm)], ['35'])).
% 8.85/9.00  thf('169', plain,
% 8.85/9.00      (![X0 : $i]:
% 8.85/9.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.85/9.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.85/9.00          | ~ (l1_struct_0 @ X0))),
% 8.85/9.00      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 8.85/9.00  thf('170', plain,
% 8.85/9.00      (![X0 : $i]:
% 8.85/9.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.85/9.00           (k1_zfmisc_1 @ 
% 8.85/9.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00          | ~ (l1_struct_0 @ X0))),
% 8.85/9.00      inference('demod', [status(thm)], ['56', '59', '62', '63', '64'])).
% 8.85/9.00  thf('171', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('172', plain,
% 8.85/9.00      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 8.85/9.00         ((v2_struct_0 @ X26)
% 8.85/9.00          | ~ (v2_pre_topc @ X26)
% 8.85/9.00          | ~ (l1_pre_topc @ X26)
% 8.85/9.00          | (v2_struct_0 @ X27)
% 8.85/9.00          | ~ (m1_pre_topc @ X27 @ X28)
% 8.85/9.00          | ~ (v1_funct_1 @ 
% 8.85/9.00               (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)))
% 8.85/9.00          | ~ (v1_funct_2 @ 
% 8.85/9.00               (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.85/9.00               (u1_struct_0 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.85/9.00               (u1_struct_0 @ X26))
% 8.85/9.00          | ~ (v5_pre_topc @ 
% 8.85/9.00               (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.85/9.00               (k1_tsep_1 @ X28 @ X30 @ X27) @ X26)
% 8.85/9.00          | ~ (m1_subset_1 @ 
% 8.85/9.00               (k2_tmap_1 @ X28 @ X26 @ X29 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.85/9.00               (k1_zfmisc_1 @ 
% 8.85/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X28 @ X30 @ X27)) @ 
% 8.85/9.00                 (u1_struct_0 @ X26))))
% 8.85/9.00          | (v5_pre_topc @ (k2_tmap_1 @ X28 @ X26 @ X29 @ X30) @ X30 @ X26)
% 8.85/9.00          | ~ (m1_subset_1 @ X29 @ 
% 8.85/9.00               (k1_zfmisc_1 @ 
% 8.85/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))))
% 8.85/9.00          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X26))
% 8.85/9.00          | ~ (v1_funct_1 @ X29)
% 8.85/9.00          | ~ (r4_tsep_1 @ X28 @ X30 @ X27)
% 8.85/9.00          | ~ (m1_pre_topc @ X30 @ X28)
% 8.85/9.00          | (v2_struct_0 @ X30)
% 8.85/9.00          | ~ (l1_pre_topc @ X28)
% 8.85/9.00          | ~ (v2_pre_topc @ X28)
% 8.85/9.00          | (v2_struct_0 @ X28))),
% 8.85/9.00      inference('cnf', [status(esa)], [t129_tmap_1])).
% 8.85/9.00  thf('173', plain,
% 8.85/9.00      (![X0 : $i, X1 : $i]:
% 8.85/9.00         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 8.85/9.00             (k1_zfmisc_1 @ 
% 8.85/9.00              (k2_zfmisc_1 @ 
% 8.85/9.00               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.85/9.00               (u1_struct_0 @ X0))))
% 8.85/9.00          | (v2_struct_0 @ sk_A)
% 8.85/9.00          | ~ (v2_pre_topc @ sk_A)
% 8.85/9.00          | ~ (l1_pre_topc @ sk_A)
% 8.85/9.00          | (v2_struct_0 @ sk_D)
% 8.85/9.00          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 8.85/9.00          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 8.85/9.00          | ~ (v1_funct_1 @ X1)
% 8.85/9.00          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 8.85/9.00          | ~ (m1_subset_1 @ X1 @ 
% 8.85/9.00               (k1_zfmisc_1 @ 
% 8.85/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 8.85/9.00          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D) @ sk_D @ X0)
% 8.85/9.00          | ~ (v5_pre_topc @ 
% 8.85/9.00               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.85/9.00               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 8.85/9.00          | ~ (v1_funct_2 @ 
% 8.85/9.00               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.85/9.00               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.85/9.00               (u1_struct_0 @ X0))
% 8.85/9.00          | ~ (v1_funct_1 @ 
% 8.85/9.00               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 8.85/9.00          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 8.85/9.00          | (v2_struct_0 @ sk_E)
% 8.85/9.00          | ~ (l1_pre_topc @ X0)
% 8.85/9.00          | ~ (v2_pre_topc @ X0)
% 8.85/9.00          | (v2_struct_0 @ X0))),
% 8.85/9.00      inference('sup-', [status(thm)], ['171', '172'])).
% 8.85/9.00  thf('174', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('175', plain, ((v2_pre_topc @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('177', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('178', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('179', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('180', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('181', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('182', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('183', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('184', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('185', plain,
% 8.85/9.00      (![X0 : $i, X1 : $i]:
% 8.85/9.00         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 8.85/9.00             (k1_zfmisc_1 @ 
% 8.85/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 8.85/9.00          | (v2_struct_0 @ sk_A)
% 8.85/9.00          | (v2_struct_0 @ sk_D)
% 8.85/9.00          | ~ (v1_funct_1 @ X1)
% 8.85/9.00          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 8.85/9.00          | ~ (m1_subset_1 @ X1 @ 
% 8.85/9.00               (k1_zfmisc_1 @ 
% 8.85/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 8.85/9.00          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D) @ sk_D @ X0)
% 8.85/9.00          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ sk_A @ X0)
% 8.85/9.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 8.85/9.00               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 8.85/9.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A))
% 8.85/9.00          | (v2_struct_0 @ sk_E)
% 8.85/9.00          | ~ (l1_pre_topc @ X0)
% 8.85/9.00          | ~ (v2_pre_topc @ X0)
% 8.85/9.00          | (v2_struct_0 @ X0))),
% 8.85/9.00      inference('demod', [status(thm)],
% 8.85/9.00                ['173', '174', '175', '176', '177', '178', '179', '180', 
% 8.85/9.00                 '181', '182', '183', '184'])).
% 8.85/9.00  thf('186', plain,
% 8.85/9.00      ((~ (l1_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | ~ (v2_pre_topc @ sk_B)
% 8.85/9.00        | ~ (l1_pre_topc @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 8.85/9.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 8.85/9.00        | ~ (m1_subset_1 @ sk_C @ 
% 8.85/9.00             (k1_zfmisc_1 @ 
% 8.85/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v1_funct_1 @ sk_C)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A))),
% 8.85/9.00      inference('sup-', [status(thm)], ['170', '185'])).
% 8.85/9.00  thf('187', plain, ((l1_struct_0 @ sk_A)),
% 8.85/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.85/9.00  thf('188', plain, ((v2_pre_topc @ sk_B)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('189', plain, ((l1_pre_topc @ sk_B)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('190', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.85/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.85/9.00  thf('191', plain,
% 8.85/9.00      ((m1_subset_1 @ sk_C @ 
% 8.85/9.00        (k1_zfmisc_1 @ 
% 8.85/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('192', plain,
% 8.85/9.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('194', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 8.85/9.00             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A))),
% 8.85/9.00      inference('demod', [status(thm)],
% 8.85/9.00                ['186', '187', '188', '189', '190', '191', '192', '193'])).
% 8.85/9.00  thf('195', plain,
% 8.85/9.00      ((~ (l1_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('sup-', [status(thm)], ['169', '194'])).
% 8.85/9.00  thf('196', plain, ((l1_struct_0 @ sk_A)),
% 8.85/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.85/9.00  thf('197', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('demod', [status(thm)], ['195', '196'])).
% 8.85/9.00  thf('198', plain,
% 8.85/9.00      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A))),
% 8.85/9.00      inference('sup-', [status(thm)], ['168', '197'])).
% 8.85/9.00  thf('199', plain,
% 8.85/9.00      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('simplify', [status(thm)], ['198'])).
% 8.85/9.00  thf('200', plain,
% 8.85/9.00      ((~ (l1_struct_0 @ sk_A)
% 8.85/9.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.85/9.00           sk_B))),
% 8.85/9.00      inference('sup-', [status(thm)], ['167', '199'])).
% 8.85/9.00  thf('201', plain, ((l1_struct_0 @ sk_A)),
% 8.85/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.85/9.00  thf('202', plain,
% 8.85/9.00      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.85/9.00           sk_B))),
% 8.85/9.00      inference('demod', [status(thm)], ['200', '201'])).
% 8.85/9.00  thf('203', plain,
% 8.85/9.00      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.85/9.00          sk_B)
% 8.85/9.00         | (v2_struct_0 @ sk_B)
% 8.85/9.00         | (v2_struct_0 @ sk_D)
% 8.85/9.00         | (v2_struct_0 @ sk_A)
% 8.85/9.00         | (v2_struct_0 @ sk_E))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['166', '202'])).
% 8.85/9.00  thf('204', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('205', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 8.85/9.00        | (v1_funct_1 @ sk_C))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('206', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 8.85/9.00         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('split', [status(esa)], ['205'])).
% 8.85/9.00  thf('207', plain,
% 8.85/9.00      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 8.85/9.00         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('sup+', [status(thm)], ['204', '206'])).
% 8.85/9.00  thf('208', plain,
% 8.85/9.00      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.85/9.00           (k1_zfmisc_1 @ 
% 8.85/9.00            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.85/9.00             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 8.85/9.00        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.85/9.00             (k1_zfmisc_1 @ 
% 8.85/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.85/9.00             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 8.85/9.00        | ~ (m1_subset_1 @ sk_C @ 
% 8.85/9.00             (k1_zfmisc_1 @ 
% 8.85/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v1_funct_1 @ sk_C))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('209', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('210', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('211', plain,
% 8.85/9.00      (![X0 : $i]:
% 8.85/9.00         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.85/9.00           (k1_zfmisc_1 @ 
% 8.85/9.00            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00          | ~ (l1_struct_0 @ X0))),
% 8.85/9.00      inference('demod', [status(thm)], ['56', '59', '62', '63', '64'])).
% 8.85/9.00  thf('212', plain,
% 8.85/9.00      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.85/9.00         (k1_zfmisc_1 @ 
% 8.85/9.00          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | ~ (l1_struct_0 @ sk_E))),
% 8.85/9.00      inference('sup+', [status(thm)], ['210', '211'])).
% 8.85/9.00  thf('213', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('214', plain,
% 8.85/9.00      (![X13 : $i, X14 : $i]:
% 8.85/9.00         (~ (m1_pre_topc @ X13 @ X14)
% 8.85/9.00          | (l1_pre_topc @ X13)
% 8.85/9.00          | ~ (l1_pre_topc @ X14))),
% 8.85/9.00      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 8.85/9.00  thf('215', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_E))),
% 8.85/9.00      inference('sup-', [status(thm)], ['213', '214'])).
% 8.85/9.00  thf('216', plain, ((l1_pre_topc @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('217', plain, ((l1_pre_topc @ sk_E)),
% 8.85/9.00      inference('demod', [status(thm)], ['215', '216'])).
% 8.85/9.00  thf('218', plain,
% 8.85/9.00      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 8.85/9.00      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.85/9.00  thf('219', plain, ((l1_struct_0 @ sk_E)),
% 8.85/9.00      inference('sup-', [status(thm)], ['217', '218'])).
% 8.85/9.00  thf('220', plain,
% 8.85/9.00      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.85/9.00        (k1_zfmisc_1 @ 
% 8.85/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 8.85/9.00      inference('demod', [status(thm)], ['212', '219'])).
% 8.85/9.00  thf('221', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('222', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('223', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('224', plain,
% 8.85/9.00      (![X0 : $i]:
% 8.85/9.00         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.85/9.00           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.85/9.00          | ~ (l1_struct_0 @ X0))),
% 8.85/9.00      inference('demod', [status(thm)], ['86', '87', '88', '89', '90'])).
% 8.85/9.00  thf('225', plain,
% 8.85/9.00      (((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.85/9.00         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (l1_struct_0 @ sk_E))),
% 8.85/9.00      inference('sup+', [status(thm)], ['223', '224'])).
% 8.85/9.00  thf('226', plain, ((l1_struct_0 @ sk_E)),
% 8.85/9.00      inference('sup-', [status(thm)], ['217', '218'])).
% 8.85/9.00  thf('227', plain,
% 8.85/9.00      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.85/9.00        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 8.85/9.00      inference('demod', [status(thm)], ['225', '226'])).
% 8.85/9.00  thf('228', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('229', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('230', plain,
% 8.85/9.00      (![X0 : $i]:
% 8.85/9.00         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.85/9.00          | ~ (l1_struct_0 @ X0))),
% 8.85/9.00      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 8.85/9.00  thf('231', plain,
% 8.85/9.00      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 8.85/9.00        | ~ (l1_struct_0 @ sk_E))),
% 8.85/9.00      inference('sup+', [status(thm)], ['229', '230'])).
% 8.85/9.00  thf('232', plain, ((l1_struct_0 @ sk_E)),
% 8.85/9.00      inference('sup-', [status(thm)], ['217', '218'])).
% 8.85/9.00  thf('233', plain,
% 8.85/9.00      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('demod', [status(thm)], ['231', '232'])).
% 8.85/9.00  thf('234', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.85/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.85/9.00  thf('235', plain,
% 8.85/9.00      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.85/9.00        (k1_zfmisc_1 @ 
% 8.85/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 8.85/9.00      inference('demod', [status(thm)], ['66', '73'])).
% 8.85/9.00  thf('236', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.85/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.85/9.00  thf('237', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.85/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.85/9.00  thf('238', plain,
% 8.85/9.00      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.85/9.00        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 8.85/9.00      inference('demod', [status(thm)], ['92', '93'])).
% 8.85/9.00  thf('239', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.85/9.00      inference('clc', [status(thm)], ['48', '49'])).
% 8.85/9.00  thf('240', plain,
% 8.85/9.00      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.85/9.00      inference('demod', [status(thm)], ['105', '106'])).
% 8.85/9.00  thf('241', plain,
% 8.85/9.00      ((m1_subset_1 @ sk_C @ 
% 8.85/9.00        (k1_zfmisc_1 @ 
% 8.85/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('242', plain,
% 8.85/9.00      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('244', plain,
% 8.85/9.00      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.85/9.00           sk_B)
% 8.85/9.00        | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('demod', [status(thm)],
% 8.85/9.00                ['208', '209', '220', '221', '222', '227', '228', '233', 
% 8.85/9.00                 '234', '235', '236', '237', '238', '239', '240', '241', 
% 8.85/9.00                 '242', '243'])).
% 8.85/9.00  thf('245', plain,
% 8.85/9.00      (((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.85/9.00              sk_D @ sk_B)))
% 8.85/9.00         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['207', '244'])).
% 8.85/9.00  thf('246', plain,
% 8.85/9.00      ((((v2_struct_0 @ sk_E)
% 8.85/9.00         | (v2_struct_0 @ sk_A)
% 8.85/9.00         | (v2_struct_0 @ sk_D)
% 8.85/9.00         | (v2_struct_0 @ sk_B)
% 8.85/9.00         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 8.85/9.00         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['203', '245'])).
% 8.85/9.00  thf('247', plain,
% 8.85/9.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 8.85/9.00         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('split', [status(esa)], ['115'])).
% 8.85/9.00  thf('248', plain,
% 8.85/9.00      ((((v2_struct_0 @ sk_E)
% 8.85/9.00         | (v2_struct_0 @ sk_A)
% 8.85/9.00         | (v2_struct_0 @ sk_D)
% 8.85/9.00         | (v2_struct_0 @ sk_B)))
% 8.85/9.00         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('demod', [status(thm)], ['246', '247'])).
% 8.85/9.00  thf('249', plain, (~ (v2_struct_0 @ sk_B)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('250', plain,
% 8.85/9.00      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 8.85/9.00         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('sup-', [status(thm)], ['248', '249'])).
% 8.85/9.00  thf('251', plain, (~ (v2_struct_0 @ sk_D)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('252', plain,
% 8.85/9.00      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 8.85/9.00         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('clc', [status(thm)], ['250', '251'])).
% 8.85/9.00  thf('253', plain, (~ (v2_struct_0 @ sk_E)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('254', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_A))
% 8.85/9.00         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.85/9.00             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('clc', [status(thm)], ['252', '253'])).
% 8.85/9.00  thf('255', plain, (~ (v2_struct_0 @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('256', plain,
% 8.85/9.00      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 8.85/9.00       ~
% 8.85/9.00       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 8.85/9.00      inference('sup-', [status(thm)], ['254', '255'])).
% 8.85/9.00  thf('257', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 8.85/9.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('258', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 8.85/9.00       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('split', [status(esa)], ['257'])).
% 8.85/9.00  thf('259', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 8.85/9.00      inference('sat_resolution*', [status(thm)], ['165', '256', '258'])).
% 8.85/9.00  thf('260', plain,
% 8.85/9.00      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)),
% 8.85/9.00      inference('simpl_trail', [status(thm)], ['114', '259'])).
% 8.85/9.00  thf('261', plain,
% 8.85/9.00      (![X0 : $i]:
% 8.85/9.00         ((v2_struct_0 @ sk_A)
% 8.85/9.00          | (v2_struct_0 @ sk_D)
% 8.85/9.00          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 8.85/9.00          | (v5_pre_topc @ 
% 8.85/9.00             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 8.85/9.00             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 8.85/9.00          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.85/9.00               (k1_zfmisc_1 @ 
% 8.85/9.00                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.85/9.00          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.85/9.00               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.85/9.00          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.85/9.00          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.85/9.00          | (v2_struct_0 @ X0)
% 8.85/9.00          | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('demod', [status(thm)], ['110', '260'])).
% 8.85/9.00  thf('262', plain,
% 8.85/9.00      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.85/9.00           (k1_zfmisc_1 @ 
% 8.85/9.00            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 8.85/9.00        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 8.85/9.00        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.85/9.00             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 8.85/9.00        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00             sk_B)
% 8.85/9.00        | (v5_pre_topc @ 
% 8.85/9.00           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.85/9.00           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 8.85/9.00        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A))),
% 8.85/9.00      inference('sup-', [status(thm)], ['43', '261'])).
% 8.85/9.00  thf('263', plain,
% 8.85/9.00      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.85/9.00        (k1_zfmisc_1 @ 
% 8.85/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 8.85/9.00      inference('demod', [status(thm)], ['212', '219'])).
% 8.85/9.00  thf('264', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('265', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('266', plain,
% 8.85/9.00      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('demod', [status(thm)], ['231', '232'])).
% 8.85/9.00  thf('267', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('268', plain,
% 8.85/9.00      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.85/9.00        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 8.85/9.00      inference('demod', [status(thm)], ['225', '226'])).
% 8.85/9.00  thf('269', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('270', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 8.85/9.00         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('split', [status(esa)], ['205'])).
% 8.85/9.00  thf('271', plain,
% 8.85/9.00      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.85/9.00         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.85/9.00      inference('clc', [status(thm)], ['41', '42'])).
% 8.85/9.00  thf('272', plain,
% 8.85/9.00      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 8.85/9.00         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.85/9.00               sk_B)))),
% 8.85/9.00      inference('demod', [status(thm)], ['270', '271'])).
% 8.85/9.00  thf('273', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 8.85/9.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('274', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 8.85/9.00       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('split', [status(esa)], ['273'])).
% 8.85/9.00  thf('275', plain,
% 8.85/9.00      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 8.85/9.00      inference('sat_resolution*', [status(thm)], ['165', '256', '274'])).
% 8.85/9.00  thf('276', plain,
% 8.85/9.00      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)),
% 8.85/9.00      inference('simpl_trail', [status(thm)], ['272', '275'])).
% 8.85/9.00  thf('277', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('278', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('279', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('280', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A))),
% 8.85/9.00      inference('demod', [status(thm)],
% 8.85/9.00                ['262', '263', '264', '265', '266', '267', '268', '269', 
% 8.85/9.00                 '276', '277', '278', '279'])).
% 8.85/9.00  thf('281', plain,
% 8.85/9.00      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('sup+', [status(thm)], ['36', '280'])).
% 8.85/9.00  thf('282', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_B)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_E)
% 8.85/9.00        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('simplify', [status(thm)], ['281'])).
% 8.85/9.00  thf('283', plain,
% 8.85/9.00      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 8.85/9.00         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.85/9.00      inference('split', [status(esa)], ['154'])).
% 8.85/9.00  thf('284', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.85/9.00      inference('sat_resolution*', [status(thm)], ['165', '256'])).
% 8.85/9.00  thf('285', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 8.85/9.00      inference('simpl_trail', [status(thm)], ['283', '284'])).
% 8.85/9.00  thf('286', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_E)
% 8.85/9.00        | (v2_struct_0 @ sk_A)
% 8.85/9.00        | (v2_struct_0 @ sk_D)
% 8.85/9.00        | (v2_struct_0 @ sk_B))),
% 8.85/9.00      inference('sup-', [status(thm)], ['282', '285'])).
% 8.85/9.00  thf('287', plain, (~ (v2_struct_0 @ sk_B)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('288', plain,
% 8.85/9.00      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E))),
% 8.85/9.00      inference('sup-', [status(thm)], ['286', '287'])).
% 8.85/9.00  thf('289', plain, (~ (v2_struct_0 @ sk_D)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('290', plain, (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A))),
% 8.85/9.00      inference('clc', [status(thm)], ['288', '289'])).
% 8.85/9.00  thf('291', plain, (~ (v2_struct_0 @ sk_E)),
% 8.85/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.00  thf('292', plain, ((v2_struct_0 @ sk_A)),
% 8.85/9.00      inference('clc', [status(thm)], ['290', '291'])).
% 8.85/9.00  thf('293', plain, ($false), inference('demod', [status(thm)], ['0', '292'])).
% 8.85/9.00  
% 8.85/9.00  % SZS output end Refutation
% 8.85/9.00  
% 8.85/9.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
