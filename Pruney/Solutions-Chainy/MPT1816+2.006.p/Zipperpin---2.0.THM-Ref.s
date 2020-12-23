%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RdG7e7dYJj

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:08 EST 2020

% Result     : Theorem 8.82s
% Output     : Refutation 8.82s
% Verified   : 
% Statistics : Number of formulae       :  335 (6037 expanded)
%              Number of leaves         :   38 (1806 expanded)
%              Depth                    :   34
%              Number of atoms          : 4587 (428460 expanded)
%              Number of equality atoms :   69 (3707 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X21 @ X20 @ X22 ) @ X21 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( ( k2_tmap_1 @ X18 @ X16 @ X19 @ X17 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) @ X19 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k2_partfun1 @ X10 @ X11 @ X9 @ X12 )
        = ( k7_relat_1 @ X9 @ X12 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( X4
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v4_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','36'])).

thf('38',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

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

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) @ X31 @ X27 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) @ X28 @ X27 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( r4_tsep_1 @ X29 @ X31 @ X28 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('54',plain,(
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
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X24 @ X25 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('60',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','64','65','66'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['55','67'])).

thf('69',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('75',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('84',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('85',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_struct_0 @ X26 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X24 @ X25 @ X23 @ X26 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['85','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('96',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('98',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_struct_0 @ X26 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X24 @ X25 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['98','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['73','74'])).

thf('109',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
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
    inference(demod,[status(thm)],['54','76','77','78','79','80','81','82','83','84','96','97','109','110','111'])).

thf('113',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('116',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('120',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['37'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('122',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','64','65','66'])).

thf('124',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) @ X27 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 ) @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( r4_tsep_1 @ X29 @ X31 @ X28 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('125',plain,(
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
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
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
    inference(demod,[status(thm)],['125','126','127','128','129','130','131','132'])).

thf('134',plain,
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
    inference('sup-',[status(thm)],['122','133'])).

thf('135',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('141',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('145',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136','137','138','139','140','141','142','143','144'])).

thf('146',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['121','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('148',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
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
    inference('sup-',[status(thm)],['120','148'])).

thf('150',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['119','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('153',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['118','153'])).

thf('155',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('156',plain,
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

thf('157',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['156'])).

thf('158',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['155','157'])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['117'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('170',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['37'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','64','65','66'])).

thf('173',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) @ X27 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X29 @ X31 @ X28 ) ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X29 @ X27 @ X30 @ X31 ) @ X31 @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( r4_tsep_1 @ X29 @ X31 @ X28 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('175',plain,(
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
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
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

thf('184',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
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
    inference(demod,[status(thm)],['175','176','177','178','179','180','181','182','183','184','185','186'])).

thf('188',plain,
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
    inference('sup-',[status(thm)],['172','187'])).

thf('189',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('190',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('193',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','189','190','191','192','193','194','195'])).

thf('197',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['171','196'])).

thf('198',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('199',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
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
    inference('sup-',[status(thm)],['170','199'])).

thf('201',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['169','201'])).

thf('203',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('204',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['168','204'])).

thf('206',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('207',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['207'])).

thf('209',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup+',[status(thm)],['206','208'])).

thf('210',plain,
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

thf('211',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('212',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','64','65','66'])).

thf('214',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('217',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('221',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['214','221'])).

thf('223',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('224',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('225',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('227',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['219','220'])).

thf('229',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('231',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('233',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['219','220'])).

thf('235',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('237',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('238',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('239',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('240',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('241',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('242',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('243',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['210','211','222','223','224','229','230','235','236','237','238','239','240','241','242','243','244','245'])).

thf('247',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['209','246'])).

thf('248',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['205','247'])).

thf('249',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['117'])).

thf('250',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['248','249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['259'])).

thf('261',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['167','258','260'])).

thf('262',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['116','261'])).

thf('263',plain,(
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
    inference(demod,[status(thm)],['112','262'])).

thf('264',plain,
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
    inference('sup-',[status(thm)],['45','263'])).

thf('265',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['214','221'])).

thf('266',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('268',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('269',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('270',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('271',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('272',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['207'])).

thf('273',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('274',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['275'])).

thf('277',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['167','258','276'])).

thf('278',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['274','277'])).

thf('279',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['264','265','266','267','268','269','270','271','278','279','280','281'])).

thf('283',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','282'])).

thf('284',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['156'])).

thf('286',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['167','258'])).

thf('287',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['284','287'])).

thf('289',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('293',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['292','293'])).

thf('295',plain,(
    $false ),
    inference(demod,[status(thm)],['0','294'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RdG7e7dYJj
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 8.82/8.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.82/8.98  % Solved by: fo/fo7.sh
% 8.82/8.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.82/8.98  % done 2808 iterations in 8.477s
% 8.82/8.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.82/8.98  % SZS output start Refutation
% 8.82/8.98  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 8.82/8.98  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 8.82/8.98  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 8.82/8.98  thf(sk_E_type, type, sk_E: $i).
% 8.82/8.98  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 8.82/8.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.82/8.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.82/8.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.82/8.98  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 8.82/8.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.82/8.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.82/8.98  thf(sk_A_type, type, sk_A: $i).
% 8.82/8.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.82/8.98  thf(sk_B_type, type, sk_B: $i).
% 8.82/8.98  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 8.82/8.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.82/8.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.82/8.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.82/8.98  thf(sk_C_type, type, sk_C: $i).
% 8.82/8.98  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 8.82/8.98  thf(sk_D_type, type, sk_D: $i).
% 8.82/8.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.82/8.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.82/8.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.82/8.98  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 8.82/8.98  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.82/8.98  thf(t132_tmap_1, conjecture,
% 8.82/8.98    (![A:$i]:
% 8.82/8.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.82/8.98       ( ![B:$i]:
% 8.82/8.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.82/8.98             ( l1_pre_topc @ B ) ) =>
% 8.82/8.98           ( ![C:$i]:
% 8.82/8.98             ( ( ( v1_funct_1 @ C ) & 
% 8.82/8.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                 ( m1_subset_1 @
% 8.82/8.98                   C @ 
% 8.82/8.98                   ( k1_zfmisc_1 @
% 8.82/8.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.82/8.98               ( ![D:$i]:
% 8.82/8.98                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 8.82/8.98                   ( ![E:$i]:
% 8.82/8.98                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 8.82/8.98                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 8.82/8.98                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 8.82/8.98                         ( ( ( v1_funct_1 @ C ) & 
% 8.82/8.98                             ( v1_funct_2 @
% 8.82/8.98                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                             ( v5_pre_topc @ C @ A @ B ) & 
% 8.82/8.98                             ( m1_subset_1 @
% 8.82/8.98                               C @ 
% 8.82/8.98                               ( k1_zfmisc_1 @
% 8.82/8.98                                 ( k2_zfmisc_1 @
% 8.82/8.98                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 8.82/8.98                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 8.82/8.98                             ( v1_funct_2 @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/8.98                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                             ( v5_pre_topc @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 8.82/8.98                             ( m1_subset_1 @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/8.98                               ( k1_zfmisc_1 @
% 8.82/8.98                                 ( k2_zfmisc_1 @
% 8.82/8.98                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.82/8.98                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 8.82/8.98                             ( v1_funct_2 @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 8.82/8.98                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                             ( v5_pre_topc @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 8.82/8.98                             ( m1_subset_1 @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 8.82/8.98                               ( k1_zfmisc_1 @
% 8.82/8.98                                 ( k2_zfmisc_1 @
% 8.82/8.98                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 8.82/8.98  thf(zf_stmt_0, negated_conjecture,
% 8.82/8.98    (~( ![A:$i]:
% 8.82/8.98        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 8.82/8.98            ( l1_pre_topc @ A ) ) =>
% 8.82/8.98          ( ![B:$i]:
% 8.82/8.98            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.82/8.98                ( l1_pre_topc @ B ) ) =>
% 8.82/8.98              ( ![C:$i]:
% 8.82/8.98                ( ( ( v1_funct_1 @ C ) & 
% 8.82/8.98                    ( v1_funct_2 @
% 8.82/8.98                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                    ( m1_subset_1 @
% 8.82/8.98                      C @ 
% 8.82/8.98                      ( k1_zfmisc_1 @
% 8.82/8.98                        ( k2_zfmisc_1 @
% 8.82/8.98                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.82/8.98                  ( ![D:$i]:
% 8.82/8.98                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 8.82/8.98                      ( ![E:$i]:
% 8.82/8.98                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 8.82/8.98                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 8.82/8.98                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 8.82/8.98                            ( ( ( v1_funct_1 @ C ) & 
% 8.82/8.98                                ( v1_funct_2 @
% 8.82/8.98                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                                ( v5_pre_topc @ C @ A @ B ) & 
% 8.82/8.98                                ( m1_subset_1 @
% 8.82/8.98                                  C @ 
% 8.82/8.98                                  ( k1_zfmisc_1 @
% 8.82/8.98                                    ( k2_zfmisc_1 @
% 8.82/8.98                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 8.82/8.98                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 8.82/8.98                                ( v1_funct_2 @
% 8.82/8.98                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/8.98                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                                ( v5_pre_topc @
% 8.82/8.98                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 8.82/8.98                                ( m1_subset_1 @
% 8.82/8.98                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/8.98                                  ( k1_zfmisc_1 @
% 8.82/8.98                                    ( k2_zfmisc_1 @
% 8.82/8.98                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.82/8.98                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 8.82/8.98                                ( v1_funct_2 @
% 8.82/8.98                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 8.82/8.98                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                                ( v5_pre_topc @
% 8.82/8.98                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 8.82/8.98                                ( m1_subset_1 @
% 8.82/8.98                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 8.82/8.98                                  ( k1_zfmisc_1 @
% 8.82/8.98                                    ( k2_zfmisc_1 @
% 8.82/8.98                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 8.82/8.98    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 8.82/8.98  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf(dt_k1_tsep_1, axiom,
% 8.82/8.98    (![A:$i,B:$i,C:$i]:
% 8.82/8.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 8.82/8.98         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 8.82/8.98         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 8.82/8.98       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 8.82/8.98         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 8.82/8.98         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 8.82/8.98  thf('3', plain,
% 8.82/8.98      (![X20 : $i, X21 : $i, X22 : $i]:
% 8.82/8.98         (~ (m1_pre_topc @ X20 @ X21)
% 8.82/8.98          | (v2_struct_0 @ X20)
% 8.82/8.98          | ~ (l1_pre_topc @ X21)
% 8.82/8.98          | (v2_struct_0 @ X21)
% 8.82/8.98          | (v2_struct_0 @ X22)
% 8.82/8.98          | ~ (m1_pre_topc @ X22 @ X21)
% 8.82/8.98          | (m1_pre_topc @ (k1_tsep_1 @ X21 @ X20 @ X22) @ X21))),
% 8.82/8.98      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 8.82/8.98  thf('4', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ X0)
% 8.82/8.98          | (v2_struct_0 @ sk_A)
% 8.82/8.98          | ~ (l1_pre_topc @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_D))),
% 8.82/8.98      inference('sup-', [status(thm)], ['2', '3'])).
% 8.82/8.98  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('6', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ X0)
% 8.82/8.98          | (v2_struct_0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_D))),
% 8.82/8.98      inference('demod', [status(thm)], ['4', '5'])).
% 8.82/8.98  thf('7', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_A))),
% 8.82/8.98      inference('sup-', [status(thm)], ['1', '6'])).
% 8.82/8.98  thf('8', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('9', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | (m1_pre_topc @ sk_A @ sk_A))),
% 8.82/8.98      inference('demod', [status(thm)], ['7', '8'])).
% 8.82/8.98  thf('10', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf(d4_tmap_1, axiom,
% 8.82/8.98    (![A:$i]:
% 8.82/8.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.82/8.98       ( ![B:$i]:
% 8.82/8.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.82/8.98             ( l1_pre_topc @ B ) ) =>
% 8.82/8.98           ( ![C:$i]:
% 8.82/8.98             ( ( ( v1_funct_1 @ C ) & 
% 8.82/8.98                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                 ( m1_subset_1 @
% 8.82/8.98                   C @ 
% 8.82/8.98                   ( k1_zfmisc_1 @
% 8.82/8.98                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.82/8.98               ( ![D:$i]:
% 8.82/8.98                 ( ( m1_pre_topc @ D @ A ) =>
% 8.82/8.98                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 8.82/8.98                     ( k2_partfun1 @
% 8.82/8.98                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 8.82/8.98                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 8.82/8.98  thf('11', plain,
% 8.82/8.98      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 8.82/8.98         ((v2_struct_0 @ X16)
% 8.82/8.98          | ~ (v2_pre_topc @ X16)
% 8.82/8.98          | ~ (l1_pre_topc @ X16)
% 8.82/8.98          | ~ (m1_pre_topc @ X17 @ X18)
% 8.82/8.98          | ((k2_tmap_1 @ X18 @ X16 @ X19 @ X17)
% 8.82/8.98              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16) @ 
% 8.82/8.98                 X19 @ (u1_struct_0 @ X17)))
% 8.82/8.98          | ~ (m1_subset_1 @ X19 @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))))
% 8.82/8.98          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X16))
% 8.82/8.98          | ~ (v1_funct_1 @ X19)
% 8.82/8.98          | ~ (l1_pre_topc @ X18)
% 8.82/8.98          | ~ (v2_pre_topc @ X18)
% 8.82/8.98          | (v2_struct_0 @ X18))),
% 8.82/8.98      inference('cnf', [status(esa)], [d4_tmap_1])).
% 8.82/8.98  thf('12', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v2_struct_0 @ sk_A)
% 8.82/8.98          | ~ (v2_pre_topc @ sk_A)
% 8.82/8.98          | ~ (l1_pre_topc @ sk_A)
% 8.82/8.98          | ~ (v1_funct_1 @ sk_C)
% 8.82/8.98          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 8.82/8.98              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.82/8.98                 sk_C @ (u1_struct_0 @ X0)))
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | ~ (l1_pre_topc @ sk_B)
% 8.82/8.98          | ~ (v2_pre_topc @ sk_B)
% 8.82/8.98          | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('sup-', [status(thm)], ['10', '11'])).
% 8.82/8.98  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('16', plain,
% 8.82/8.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('17', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf(redefinition_k2_partfun1, axiom,
% 8.82/8.98    (![A:$i,B:$i,C:$i,D:$i]:
% 8.82/8.98     ( ( ( v1_funct_1 @ C ) & 
% 8.82/8.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.82/8.98       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 8.82/8.98  thf('18', plain,
% 8.82/8.98      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 8.82/8.98         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 8.82/8.98          | ~ (v1_funct_1 @ X9)
% 8.82/8.98          | ((k2_partfun1 @ X10 @ X11 @ X9 @ X12) = (k7_relat_1 @ X9 @ X12)))),
% 8.82/8.98      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 8.82/8.98  thf('19', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 8.82/8.98            X0) = (k7_relat_1 @ sk_C @ X0))
% 8.82/8.98          | ~ (v1_funct_1 @ sk_C))),
% 8.82/8.98      inference('sup-', [status(thm)], ['17', '18'])).
% 8.82/8.98  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('21', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 8.82/8.98           X0) = (k7_relat_1 @ sk_C @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['19', '20'])).
% 8.82/8.98  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('24', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v2_struct_0 @ sk_A)
% 8.82/8.98          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 8.82/8.98              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('demod', [status(thm)],
% 8.82/8.98                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 8.82/8.98  thf('25', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_E)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 8.82/8.98            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 8.82/8.98        | (v2_struct_0 @ sk_A))),
% 8.82/8.98      inference('sup-', [status(thm)], ['9', '24'])).
% 8.82/8.98  thf('26', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf(cc2_relset_1, axiom,
% 8.82/8.98    (![A:$i,B:$i,C:$i]:
% 8.82/8.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.82/8.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.82/8.98  thf('27', plain,
% 8.82/8.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 8.82/8.98         ((v4_relat_1 @ X6 @ X7)
% 8.82/8.98          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 8.82/8.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.82/8.98  thf('28', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 8.82/8.98      inference('sup-', [status(thm)], ['26', '27'])).
% 8.82/8.98  thf(t209_relat_1, axiom,
% 8.82/8.98    (![A:$i,B:$i]:
% 8.82/8.98     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 8.82/8.98       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 8.82/8.98  thf('29', plain,
% 8.82/8.98      (![X4 : $i, X5 : $i]:
% 8.82/8.98         (((X4) = (k7_relat_1 @ X4 @ X5))
% 8.82/8.98          | ~ (v4_relat_1 @ X4 @ X5)
% 8.82/8.98          | ~ (v1_relat_1 @ X4))),
% 8.82/8.98      inference('cnf', [status(esa)], [t209_relat_1])).
% 8.82/8.98  thf('30', plain,
% 8.82/8.98      ((~ (v1_relat_1 @ sk_C)
% 8.82/8.98        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 8.82/8.98      inference('sup-', [status(thm)], ['28', '29'])).
% 8.82/8.98  thf('31', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf(cc2_relat_1, axiom,
% 8.82/8.98    (![A:$i]:
% 8.82/8.98     ( ( v1_relat_1 @ A ) =>
% 8.82/8.98       ( ![B:$i]:
% 8.82/8.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.82/8.98  thf('32', plain,
% 8.82/8.98      (![X0 : $i, X1 : $i]:
% 8.82/8.98         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 8.82/8.98          | (v1_relat_1 @ X0)
% 8.82/8.98          | ~ (v1_relat_1 @ X1))),
% 8.82/8.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.82/8.98  thf('33', plain,
% 8.82/8.98      ((~ (v1_relat_1 @ 
% 8.82/8.98           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 8.82/8.98        | (v1_relat_1 @ sk_C))),
% 8.82/8.98      inference('sup-', [status(thm)], ['31', '32'])).
% 8.82/8.98  thf(fc6_relat_1, axiom,
% 8.82/8.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.82/8.98  thf('34', plain,
% 8.82/8.98      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 8.82/8.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.82/8.98  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 8.82/8.98      inference('demod', [status(thm)], ['33', '34'])).
% 8.82/8.98  thf('36', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 8.82/8.98      inference('demod', [status(thm)], ['30', '35'])).
% 8.82/8.98  thf('37', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_E)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 8.82/8.98        | (v2_struct_0 @ sk_A))),
% 8.82/8.98      inference('demod', [status(thm)], ['25', '36'])).
% 8.82/8.98  thf('38', plain,
% 8.82/8.98      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_E))),
% 8.82/8.98      inference('simplify', [status(thm)], ['37'])).
% 8.82/8.98  thf('39', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('40', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v2_struct_0 @ sk_A)
% 8.82/8.98          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 8.82/8.98              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('demod', [status(thm)],
% 8.82/8.98                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 8.82/8.98  thf('41', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_B)
% 8.82/8.98        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.98            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 8.82/8.98        | (v2_struct_0 @ sk_A))),
% 8.82/8.98      inference('sup-', [status(thm)], ['39', '40'])).
% 8.82/8.98  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('43', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_A)
% 8.82/8.98        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.98            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))),
% 8.82/8.98      inference('clc', [status(thm)], ['41', '42'])).
% 8.82/8.98  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('45', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.98      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.98  thf('46', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('47', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v2_struct_0 @ sk_A)
% 8.82/8.98          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 8.82/8.98              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('demod', [status(thm)],
% 8.82/8.98                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 8.82/8.98  thf('48', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_B)
% 8.82/8.98        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 8.82/8.98        | (v2_struct_0 @ sk_A))),
% 8.82/8.98      inference('sup-', [status(thm)], ['46', '47'])).
% 8.82/8.98  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('50', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_A)
% 8.82/8.98        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))),
% 8.82/8.98      inference('clc', [status(thm)], ['48', '49'])).
% 8.82/8.98  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('52', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf(t129_tmap_1, axiom,
% 8.82/8.98    (![A:$i]:
% 8.82/8.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.82/8.98       ( ![B:$i]:
% 8.82/8.98         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 8.82/8.98             ( l1_pre_topc @ B ) ) =>
% 8.82/8.98           ( ![C:$i]:
% 8.82/8.98             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 8.82/8.98               ( ![D:$i]:
% 8.82/8.98                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 8.82/8.98                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 8.82/8.98                     ( ![E:$i]:
% 8.82/8.98                       ( ( ( v1_funct_1 @ E ) & 
% 8.82/8.98                           ( v1_funct_2 @
% 8.82/8.98                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                           ( m1_subset_1 @
% 8.82/8.98                             E @ 
% 8.82/8.98                             ( k1_zfmisc_1 @
% 8.82/8.98                               ( k2_zfmisc_1 @
% 8.82/8.98                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.82/8.98                         ( ( ( v1_funct_1 @
% 8.82/8.98                               ( k2_tmap_1 @
% 8.82/8.98                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 8.82/8.98                             ( v1_funct_2 @
% 8.82/8.98                               ( k2_tmap_1 @
% 8.82/8.98                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/8.98                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/8.98                               ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                             ( v5_pre_topc @
% 8.82/8.98                               ( k2_tmap_1 @
% 8.82/8.98                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/8.98                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 8.82/8.98                             ( m1_subset_1 @
% 8.82/8.98                               ( k2_tmap_1 @
% 8.82/8.98                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/8.98                               ( k1_zfmisc_1 @
% 8.82/8.98                                 ( k2_zfmisc_1 @
% 8.82/8.98                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 8.82/8.98                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 8.82/8.98                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 8.82/8.98                             ( v1_funct_2 @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 8.82/8.98                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                             ( v5_pre_topc @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 8.82/8.98                             ( m1_subset_1 @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 8.82/8.98                               ( k1_zfmisc_1 @
% 8.82/8.98                                 ( k2_zfmisc_1 @
% 8.82/8.98                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.82/8.98                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 8.82/8.98                             ( v1_funct_2 @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 8.82/8.98                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98                             ( v5_pre_topc @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 8.82/8.98                             ( m1_subset_1 @
% 8.82/8.98                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 8.82/8.98                               ( k1_zfmisc_1 @
% 8.82/8.98                                 ( k2_zfmisc_1 @
% 8.82/8.98                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 8.82/8.98  thf('53', plain,
% 8.82/8.98      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 8.82/8.98         ((v2_struct_0 @ X27)
% 8.82/8.98          | ~ (v2_pre_topc @ X27)
% 8.82/8.98          | ~ (l1_pre_topc @ X27)
% 8.82/8.98          | (v2_struct_0 @ X28)
% 8.82/8.98          | ~ (m1_pre_topc @ X28 @ X29)
% 8.82/8.98          | ~ (v1_funct_1 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31))
% 8.82/8.98          | ~ (v1_funct_2 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31) @ 
% 8.82/8.98               (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))
% 8.82/8.98          | ~ (v5_pre_topc @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31) @ X31 @ X27)
% 8.82/8.98          | ~ (m1_subset_1 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31) @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X27))))
% 8.82/8.98          | ~ (v1_funct_1 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28))
% 8.82/8.98          | ~ (v1_funct_2 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28) @ 
% 8.82/8.98               (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 8.82/8.98          | ~ (v5_pre_topc @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28) @ X28 @ X27)
% 8.82/8.98          | ~ (m1_subset_1 @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28) @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))))
% 8.82/8.98          | (v5_pre_topc @ 
% 8.82/8.98             (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98             (k1_tsep_1 @ X29 @ X31 @ X28) @ X27)
% 8.82/8.98          | ~ (m1_subset_1 @ X30 @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 8.82/8.98          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 8.82/8.98          | ~ (v1_funct_1 @ X30)
% 8.82/8.98          | ~ (r4_tsep_1 @ X29 @ X31 @ X28)
% 8.82/8.98          | ~ (m1_pre_topc @ X31 @ X29)
% 8.82/8.98          | (v2_struct_0 @ X31)
% 8.82/8.98          | ~ (l1_pre_topc @ X29)
% 8.82/8.98          | ~ (v2_pre_topc @ X29)
% 8.82/8.98          | (v2_struct_0 @ X29))),
% 8.82/8.98      inference('cnf', [status(esa)], [t129_tmap_1])).
% 8.82/8.98  thf('54', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         (~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | (v2_struct_0 @ sk_A)
% 8.82/8.98          | ~ (v2_pre_topc @ sk_A)
% 8.82/8.98          | ~ (l1_pre_topc @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_D)
% 8.82/8.98          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 8.82/8.98          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 8.82/8.98          | ~ (v1_funct_1 @ sk_C)
% 8.82/8.98          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (m1_subset_1 @ sk_C @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | (v5_pre_topc @ 
% 8.82/8.98             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 8.82/8.98             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 8.82/8.98          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.82/8.98          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/8.98          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.82/8.98               sk_B)
% 8.82/8.98          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.82/8.98               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ X0)
% 8.82/8.98          | ~ (l1_pre_topc @ sk_B)
% 8.82/8.98          | ~ (v2_pre_topc @ sk_B)
% 8.82/8.98          | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('sup-', [status(thm)], ['52', '53'])).
% 8.82/8.98  thf('55', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf('56', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf(dt_k2_tmap_1, axiom,
% 8.82/8.98    (![A:$i,B:$i,C:$i,D:$i]:
% 8.82/8.98     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 8.82/8.98         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.82/8.98         ( m1_subset_1 @
% 8.82/8.98           C @ 
% 8.82/8.98           ( k1_zfmisc_1 @
% 8.82/8.98             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 8.82/8.98         ( l1_struct_0 @ D ) ) =>
% 8.82/8.98       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 8.82/8.98         ( v1_funct_2 @
% 8.82/8.98           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 8.82/8.98           ( u1_struct_0 @ B ) ) & 
% 8.82/8.98         ( m1_subset_1 @
% 8.82/8.98           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 8.82/8.98           ( k1_zfmisc_1 @
% 8.82/8.98             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 8.82/8.98  thf('57', plain,
% 8.82/8.98      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 8.82/8.98         (~ (m1_subset_1 @ X23 @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 8.82/8.98          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 8.82/8.98          | ~ (v1_funct_1 @ X23)
% 8.82/8.98          | ~ (l1_struct_0 @ X25)
% 8.82/8.98          | ~ (l1_struct_0 @ X24)
% 8.82/8.98          | ~ (l1_struct_0 @ X26)
% 8.82/8.98          | (m1_subset_1 @ (k2_tmap_1 @ X24 @ X25 @ X23 @ X26) @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25)))))),
% 8.82/8.98      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 8.82/8.98  thf('58', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98           (k1_zfmisc_1 @ 
% 8.82/8.98            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | ~ (l1_struct_0 @ X0)
% 8.82/8.98          | ~ (l1_struct_0 @ sk_A)
% 8.82/8.98          | ~ (l1_struct_0 @ sk_B)
% 8.82/8.98          | ~ (v1_funct_1 @ sk_C)
% 8.82/8.98          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 8.82/8.98      inference('sup-', [status(thm)], ['56', '57'])).
% 8.82/8.98  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf(dt_l1_pre_topc, axiom,
% 8.82/8.98    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 8.82/8.98  thf('60', plain,
% 8.82/8.98      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 8.82/8.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.82/8.98  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.98      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.98  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('63', plain,
% 8.82/8.98      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 8.82/8.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.82/8.98  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 8.82/8.98      inference('sup-', [status(thm)], ['62', '63'])).
% 8.82/8.98  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('66', plain,
% 8.82/8.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('67', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98           (k1_zfmisc_1 @ 
% 8.82/8.98            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['58', '61', '64', '65', '66'])).
% 8.82/8.98  thf('68', plain,
% 8.82/8.98      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.98         (k1_zfmisc_1 @ 
% 8.82/8.98          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98        | ~ (l1_struct_0 @ sk_D))),
% 8.82/8.98      inference('sup+', [status(thm)], ['55', '67'])).
% 8.82/8.98  thf('69', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf(dt_m1_pre_topc, axiom,
% 8.82/8.98    (![A:$i]:
% 8.82/8.98     ( ( l1_pre_topc @ A ) =>
% 8.82/8.98       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 8.82/8.98  thf('70', plain,
% 8.82/8.98      (![X14 : $i, X15 : $i]:
% 8.82/8.98         (~ (m1_pre_topc @ X14 @ X15)
% 8.82/8.98          | (l1_pre_topc @ X14)
% 8.82/8.98          | ~ (l1_pre_topc @ X15))),
% 8.82/8.98      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 8.82/8.98  thf('71', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 8.82/8.98      inference('sup-', [status(thm)], ['69', '70'])).
% 8.82/8.98  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('73', plain, ((l1_pre_topc @ sk_D)),
% 8.82/8.98      inference('demod', [status(thm)], ['71', '72'])).
% 8.82/8.98  thf('74', plain,
% 8.82/8.98      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 8.82/8.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.82/8.98  thf('75', plain, ((l1_struct_0 @ sk_D)),
% 8.82/8.98      inference('sup-', [status(thm)], ['73', '74'])).
% 8.82/8.98  thf('76', plain,
% 8.82/8.98      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('demod', [status(thm)], ['68', '75'])).
% 8.82/8.98  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('79', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('81', plain,
% 8.82/8.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('82', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('83', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf('84', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf('85', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf('86', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('87', plain,
% 8.82/8.98      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 8.82/8.98         (~ (m1_subset_1 @ X23 @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 8.82/8.98          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 8.82/8.98          | ~ (v1_funct_1 @ X23)
% 8.82/8.98          | ~ (l1_struct_0 @ X25)
% 8.82/8.98          | ~ (l1_struct_0 @ X24)
% 8.82/8.98          | ~ (l1_struct_0 @ X26)
% 8.82/8.98          | (v1_funct_2 @ (k2_tmap_1 @ X24 @ X25 @ X23 @ X26) @ 
% 8.82/8.98             (u1_struct_0 @ X26) @ (u1_struct_0 @ X25)))),
% 8.82/8.98      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 8.82/8.98  thf('88', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (l1_struct_0 @ X0)
% 8.82/8.98          | ~ (l1_struct_0 @ sk_A)
% 8.82/8.98          | ~ (l1_struct_0 @ sk_B)
% 8.82/8.98          | ~ (v1_funct_1 @ sk_C)
% 8.82/8.98          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 8.82/8.98      inference('sup-', [status(thm)], ['86', '87'])).
% 8.82/8.98  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.98      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.98  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 8.82/8.98      inference('sup-', [status(thm)], ['62', '63'])).
% 8.82/8.98  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('92', plain,
% 8.82/8.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('93', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 8.82/8.98  thf('94', plain,
% 8.82/8.98      (((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.98         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 8.82/8.98        | ~ (l1_struct_0 @ sk_D))),
% 8.82/8.98      inference('sup+', [status(thm)], ['85', '93'])).
% 8.82/8.98  thf('95', plain, ((l1_struct_0 @ sk_D)),
% 8.82/8.98      inference('sup-', [status(thm)], ['73', '74'])).
% 8.82/8.98  thf('96', plain,
% 8.82/8.98      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.98        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 8.82/8.98      inference('demod', [status(thm)], ['94', '95'])).
% 8.82/8.98  thf('97', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf('98', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf('99', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('100', plain,
% 8.82/8.98      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 8.82/8.98         (~ (m1_subset_1 @ X23 @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))))
% 8.82/8.98          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 8.82/8.98          | ~ (v1_funct_1 @ X23)
% 8.82/8.98          | ~ (l1_struct_0 @ X25)
% 8.82/8.98          | ~ (l1_struct_0 @ X24)
% 8.82/8.98          | ~ (l1_struct_0 @ X26)
% 8.82/8.98          | (v1_funct_1 @ (k2_tmap_1 @ X24 @ X25 @ X23 @ X26)))),
% 8.82/8.98      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 8.82/8.98  thf('101', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/8.98          | ~ (l1_struct_0 @ X0)
% 8.82/8.98          | ~ (l1_struct_0 @ sk_A)
% 8.82/8.98          | ~ (l1_struct_0 @ sk_B)
% 8.82/8.98          | ~ (v1_funct_1 @ sk_C)
% 8.82/8.98          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 8.82/8.98      inference('sup-', [status(thm)], ['99', '100'])).
% 8.82/8.98  thf('102', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.98      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.98  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 8.82/8.98      inference('sup-', [status(thm)], ['62', '63'])).
% 8.82/8.98  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('105', plain,
% 8.82/8.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('106', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 8.82/8.98  thf('107', plain,
% 8.82/8.98      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 8.82/8.98        | ~ (l1_struct_0 @ sk_D))),
% 8.82/8.98      inference('sup+', [status(thm)], ['98', '106'])).
% 8.82/8.98  thf('108', plain, ((l1_struct_0 @ sk_D)),
% 8.82/8.98      inference('sup-', [status(thm)], ['73', '74'])).
% 8.82/8.98  thf('109', plain,
% 8.82/8.98      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('demod', [status(thm)], ['107', '108'])).
% 8.82/8.98  thf('110', plain, ((l1_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('111', plain, ((v2_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('112', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v2_struct_0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_D)
% 8.82/8.98          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 8.82/8.98          | (v5_pre_topc @ 
% 8.82/8.98             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 8.82/8.98             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 8.82/8.98          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.82/8.98          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/8.98          | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.98               sk_D @ sk_B)
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ X0)
% 8.82/8.98          | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('demod', [status(thm)],
% 8.82/8.98                ['54', '76', '77', '78', '79', '80', '81', '82', '83', '84', 
% 8.82/8.98                 '96', '97', '109', '110', '111'])).
% 8.82/8.98  thf('113', plain,
% 8.82/8.98      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 8.82/8.98        | (v1_funct_1 @ sk_C))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('114', plain,
% 8.82/8.98      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 8.82/8.98         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.82/8.98               sk_B)))),
% 8.82/8.98      inference('split', [status(esa)], ['113'])).
% 8.82/8.98  thf('115', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf('116', plain,
% 8.82/8.98      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B))
% 8.82/8.98         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.82/8.98               sk_B)))),
% 8.82/8.98      inference('demod', [status(thm)], ['114', '115'])).
% 8.82/8.98  thf('117', plain,
% 8.82/8.98      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 8.82/8.98        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('118', plain,
% 8.82/8.98      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 8.82/8.98         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.98      inference('split', [status(esa)], ['117'])).
% 8.82/8.98  thf('119', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 8.82/8.98  thf('120', plain,
% 8.82/8.98      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_E))),
% 8.82/8.98      inference('simplify', [status(thm)], ['37'])).
% 8.82/8.98  thf('121', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 8.82/8.98  thf('122', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('123', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98           (k1_zfmisc_1 @ 
% 8.82/8.98            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['58', '61', '64', '65', '66'])).
% 8.82/8.98  thf('124', plain,
% 8.82/8.98      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 8.82/8.98         ((v2_struct_0 @ X27)
% 8.82/8.98          | ~ (v2_pre_topc @ X27)
% 8.82/8.98          | ~ (l1_pre_topc @ X27)
% 8.82/8.98          | (v2_struct_0 @ X28)
% 8.82/8.98          | ~ (m1_pre_topc @ X28 @ X29)
% 8.82/8.98          | ~ (v1_funct_1 @ 
% 8.82/8.98               (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)))
% 8.82/8.98          | ~ (v1_funct_2 @ 
% 8.82/8.98               (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98               (u1_struct_0 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98               (u1_struct_0 @ X27))
% 8.82/8.98          | ~ (v5_pre_topc @ 
% 8.82/8.98               (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98               (k1_tsep_1 @ X29 @ X31 @ X28) @ X27)
% 8.82/8.98          | ~ (m1_subset_1 @ 
% 8.82/8.98               (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98                 (u1_struct_0 @ X27))))
% 8.82/8.98          | (v5_pre_topc @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X28) @ X28 @ X27)
% 8.82/8.98          | ~ (m1_subset_1 @ X30 @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 8.82/8.98          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 8.82/8.98          | ~ (v1_funct_1 @ X30)
% 8.82/8.98          | ~ (r4_tsep_1 @ X29 @ X31 @ X28)
% 8.82/8.98          | ~ (m1_pre_topc @ X31 @ X29)
% 8.82/8.98          | (v2_struct_0 @ X31)
% 8.82/8.98          | ~ (l1_pre_topc @ X29)
% 8.82/8.98          | ~ (v2_pre_topc @ X29)
% 8.82/8.98          | (v2_struct_0 @ X29))),
% 8.82/8.98      inference('cnf', [status(esa)], [t129_tmap_1])).
% 8.82/8.98  thf('125', plain,
% 8.82/8.98      (![X0 : $i, X1 : $i]:
% 8.82/8.98         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 8.82/8.98          | (v2_struct_0 @ sk_A)
% 8.82/8.98          | ~ (v2_pre_topc @ sk_A)
% 8.82/8.98          | ~ (l1_pre_topc @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ X1)
% 8.82/8.98          | ~ (m1_pre_topc @ X1 @ sk_A)
% 8.82/8.98          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 8.82/8.98          | ~ (v1_funct_1 @ sk_C)
% 8.82/8.98          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (m1_subset_1 @ sk_C @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.82/8.98          | ~ (v5_pre_topc @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.82/8.98               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 8.82/8.98          | ~ (v1_funct_2 @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.82/8.98               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.82/8.98               (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (v1_funct_1 @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ X0)
% 8.82/8.98          | ~ (l1_pre_topc @ sk_B)
% 8.82/8.98          | ~ (v2_pre_topc @ sk_B)
% 8.82/8.98          | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('sup-', [status(thm)], ['123', '124'])).
% 8.82/8.98  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('129', plain,
% 8.82/8.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('130', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('132', plain, ((v2_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('133', plain,
% 8.82/8.98      (![X0 : $i, X1 : $i]:
% 8.82/8.98         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 8.82/8.98          | (v2_struct_0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ X1)
% 8.82/8.98          | ~ (m1_pre_topc @ X1 @ sk_A)
% 8.82/8.98          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 8.82/8.98          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.82/8.98          | ~ (v5_pre_topc @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.82/8.98               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 8.82/8.98          | ~ (v1_funct_2 @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.82/8.98               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 8.82/8.98               (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (v1_funct_1 @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 8.82/8.98          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ X0)
% 8.82/8.98          | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('demod', [status(thm)],
% 8.82/8.98                ['125', '126', '127', '128', '129', '130', '131', '132'])).
% 8.82/8.98  thf('134', plain,
% 8.82/8.98      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 8.82/8.98           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.82/8.98           (u1_struct_0 @ sk_B))
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 8.82/8.98        | ~ (v1_funct_1 @ 
% 8.82/8.98             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 8.82/8.98        | ~ (v5_pre_topc @ 
% 8.82/8.98             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.82/8.98             (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 8.82/8.98        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 8.82/8.98        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 8.82/8.98        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))),
% 8.82/8.98      inference('sup-', [status(thm)], ['122', '133'])).
% 8.82/8.98  thf('135', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('136', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('137', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('138', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('139', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('140', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.98      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.98  thf('141', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('142', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('143', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('144', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.98      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.98  thf('145', plain,
% 8.82/8.98      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 8.82/8.98           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.98        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.82/8.98             sk_B)
% 8.82/8.98        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.98           sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A))),
% 8.82/8.98      inference('demod', [status(thm)],
% 8.82/8.98                ['134', '135', '136', '137', '138', '139', '140', '141', 
% 8.82/8.98                 '142', '143', '144'])).
% 8.82/8.98  thf('146', plain,
% 8.82/8.98      ((~ (l1_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.98           sk_B)
% 8.82/8.98        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.82/8.98             sk_B)
% 8.82/8.98        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('sup-', [status(thm)], ['121', '145'])).
% 8.82/8.98  thf('147', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.98      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.98  thf('148', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.98           sk_B)
% 8.82/8.98        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.82/8.98             sk_B)
% 8.82/8.98        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | (v2_struct_0 @ sk_B))),
% 8.82/8.98      inference('demod', [status(thm)], ['146', '147'])).
% 8.82/8.98  thf('149', plain,
% 8.82/8.98      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.98        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.98           sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A))),
% 8.82/8.98      inference('sup-', [status(thm)], ['120', '148'])).
% 8.82/8.98  thf('150', plain,
% 8.82/8.98      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)
% 8.82/8.98        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.98      inference('simplify', [status(thm)], ['149'])).
% 8.82/8.98  thf('151', plain,
% 8.82/8.98      ((~ (l1_struct_0 @ sk_A)
% 8.82/8.98        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.98           sk_B))),
% 8.82/8.98      inference('sup-', [status(thm)], ['119', '150'])).
% 8.82/8.98  thf('152', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.98      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.98  thf('153', plain,
% 8.82/8.98      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.98           sk_B))),
% 8.82/8.98      inference('demod', [status(thm)], ['151', '152'])).
% 8.82/8.98  thf('154', plain,
% 8.82/8.98      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.98          sk_B)
% 8.82/8.98         | (v2_struct_0 @ sk_B)
% 8.82/8.98         | (v2_struct_0 @ sk_D)
% 8.82/8.98         | (v2_struct_0 @ sk_A)
% 8.82/8.98         | (v2_struct_0 @ sk_E))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.98      inference('sup-', [status(thm)], ['118', '153'])).
% 8.82/8.98  thf('155', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.98      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.98  thf('156', plain,
% 8.82/8.98      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.82/8.98           (k1_zfmisc_1 @ 
% 8.82/8.98            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.98             sk_B)
% 8.82/8.98        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.82/8.98             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 8.82/8.98        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 8.82/8.98        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.82/8.98             sk_B)
% 8.82/8.98        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.82/8.98             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 8.82/8.98        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 8.82/8.98        | ~ (m1_subset_1 @ sk_C @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.98        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.98        | ~ (v1_funct_1 @ sk_C))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('157', plain,
% 8.82/8.98      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 8.82/8.98         <= (~
% 8.82/8.98             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.98               sk_B)))),
% 8.82/8.98      inference('split', [status(esa)], ['156'])).
% 8.82/8.98  thf('158', plain,
% 8.82/8.98      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.98           sk_B))
% 8.82/8.98         <= (~
% 8.82/8.98             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.98               sk_B)))),
% 8.82/8.98      inference('sup-', [status(thm)], ['155', '157'])).
% 8.82/8.98  thf('159', plain,
% 8.82/8.98      ((((v2_struct_0 @ sk_E)
% 8.82/8.98         | (v2_struct_0 @ sk_A)
% 8.82/8.98         | (v2_struct_0 @ sk_D)
% 8.82/8.98         | (v2_struct_0 @ sk_B)))
% 8.82/8.98         <= (~
% 8.82/8.98             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.98               sk_B)) & 
% 8.82/8.98             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.98      inference('sup-', [status(thm)], ['154', '158'])).
% 8.82/8.98  thf('160', plain, (~ (v2_struct_0 @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('161', plain,
% 8.82/8.98      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 8.82/8.98         <= (~
% 8.82/8.98             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.98               sk_B)) & 
% 8.82/8.98             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.98      inference('sup-', [status(thm)], ['159', '160'])).
% 8.82/8.98  thf('162', plain, (~ (v2_struct_0 @ sk_D)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('163', plain,
% 8.82/8.98      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 8.82/8.98         <= (~
% 8.82/8.98             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.98               sk_B)) & 
% 8.82/8.98             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.98      inference('clc', [status(thm)], ['161', '162'])).
% 8.82/8.98  thf('164', plain, (~ (v2_struct_0 @ sk_E)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('165', plain,
% 8.82/8.98      (((v2_struct_0 @ sk_A))
% 8.82/8.98         <= (~
% 8.82/8.98             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.98               sk_B)) & 
% 8.82/8.98             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.98      inference('clc', [status(thm)], ['163', '164'])).
% 8.82/8.98  thf('166', plain, (~ (v2_struct_0 @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('167', plain,
% 8.82/8.98      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 8.82/8.98       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.98      inference('sup-', [status(thm)], ['165', '166'])).
% 8.82/8.98  thf('168', plain,
% 8.82/8.98      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 8.82/8.98         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.98      inference('split', [status(esa)], ['117'])).
% 8.82/8.98  thf('169', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 8.82/8.98  thf('170', plain,
% 8.82/8.98      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_E))),
% 8.82/8.98      inference('simplify', [status(thm)], ['37'])).
% 8.82/8.98  thf('171', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 8.82/8.98  thf('172', plain,
% 8.82/8.98      (![X0 : $i]:
% 8.82/8.98         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.98           (k1_zfmisc_1 @ 
% 8.82/8.98            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98          | ~ (l1_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)], ['58', '61', '64', '65', '66'])).
% 8.82/8.98  thf('173', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('174', plain,
% 8.82/8.98      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 8.82/8.98         ((v2_struct_0 @ X27)
% 8.82/8.98          | ~ (v2_pre_topc @ X27)
% 8.82/8.98          | ~ (l1_pre_topc @ X27)
% 8.82/8.98          | (v2_struct_0 @ X28)
% 8.82/8.98          | ~ (m1_pre_topc @ X28 @ X29)
% 8.82/8.98          | ~ (v1_funct_1 @ 
% 8.82/8.98               (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)))
% 8.82/8.98          | ~ (v1_funct_2 @ 
% 8.82/8.98               (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98               (u1_struct_0 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98               (u1_struct_0 @ X27))
% 8.82/8.98          | ~ (v5_pre_topc @ 
% 8.82/8.98               (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98               (k1_tsep_1 @ X29 @ X31 @ X28) @ X27)
% 8.82/8.98          | ~ (m1_subset_1 @ 
% 8.82/8.98               (k2_tmap_1 @ X29 @ X27 @ X30 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X29 @ X31 @ X28)) @ 
% 8.82/8.98                 (u1_struct_0 @ X27))))
% 8.82/8.98          | (v5_pre_topc @ (k2_tmap_1 @ X29 @ X27 @ X30 @ X31) @ X31 @ X27)
% 8.82/8.98          | ~ (m1_subset_1 @ X30 @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 8.82/8.98          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 8.82/8.98          | ~ (v1_funct_1 @ X30)
% 8.82/8.98          | ~ (r4_tsep_1 @ X29 @ X31 @ X28)
% 8.82/8.98          | ~ (m1_pre_topc @ X31 @ X29)
% 8.82/8.98          | (v2_struct_0 @ X31)
% 8.82/8.98          | ~ (l1_pre_topc @ X29)
% 8.82/8.98          | ~ (v2_pre_topc @ X29)
% 8.82/8.98          | (v2_struct_0 @ X29))),
% 8.82/8.98      inference('cnf', [status(esa)], [t129_tmap_1])).
% 8.82/8.98  thf('175', plain,
% 8.82/8.98      (![X0 : $i, X1 : $i]:
% 8.82/8.98         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ 
% 8.82/8.98               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.82/8.98               (u1_struct_0 @ X0))))
% 8.82/8.98          | (v2_struct_0 @ sk_A)
% 8.82/8.98          | ~ (v2_pre_topc @ sk_A)
% 8.82/8.98          | ~ (l1_pre_topc @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_D)
% 8.82/8.98          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 8.82/8.98          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 8.82/8.98          | ~ (v1_funct_1 @ X1)
% 8.82/8.98          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 8.82/8.98          | ~ (m1_subset_1 @ X1 @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 8.82/8.98          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D) @ sk_D @ X0)
% 8.82/8.98          | ~ (v5_pre_topc @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.82/8.98               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 8.82/8.98          | ~ (v1_funct_2 @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.82/8.98               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.82/8.98               (u1_struct_0 @ X0))
% 8.82/8.98          | ~ (v1_funct_1 @ 
% 8.82/8.98               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 8.82/8.98          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_E)
% 8.82/8.98          | ~ (l1_pre_topc @ X0)
% 8.82/8.98          | ~ (v2_pre_topc @ X0)
% 8.82/8.98          | (v2_struct_0 @ X0))),
% 8.82/8.98      inference('sup-', [status(thm)], ['173', '174'])).
% 8.82/8.98  thf('176', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('179', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('180', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('181', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('182', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('183', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('184', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('185', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('186', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('187', plain,
% 8.82/8.98      (![X0 : $i, X1 : $i]:
% 8.82/8.98         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 8.82/8.98          | (v2_struct_0 @ sk_A)
% 8.82/8.98          | (v2_struct_0 @ sk_D)
% 8.82/8.98          | ~ (v1_funct_1 @ X1)
% 8.82/8.98          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 8.82/8.98          | ~ (m1_subset_1 @ X1 @ 
% 8.82/8.98               (k1_zfmisc_1 @ 
% 8.82/8.98                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 8.82/8.98          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D) @ sk_D @ X0)
% 8.82/8.98          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ sk_A @ X0)
% 8.82/8.98          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 8.82/8.98               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 8.82/8.98          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A))
% 8.82/8.98          | (v2_struct_0 @ sk_E)
% 8.82/8.98          | ~ (l1_pre_topc @ X0)
% 8.82/8.98          | ~ (v2_pre_topc @ X0)
% 8.82/8.98          | (v2_struct_0 @ X0))),
% 8.82/8.98      inference('demod', [status(thm)],
% 8.82/8.98                ['175', '176', '177', '178', '179', '180', '181', '182', 
% 8.82/8.98                 '183', '184', '185', '186'])).
% 8.82/8.98  thf('188', plain,
% 8.82/8.98      ((~ (l1_struct_0 @ sk_A)
% 8.82/8.98        | (v2_struct_0 @ sk_B)
% 8.82/8.98        | ~ (v2_pre_topc @ sk_B)
% 8.82/8.98        | ~ (l1_pre_topc @ sk_B)
% 8.82/8.98        | (v2_struct_0 @ sk_E)
% 8.82/8.98        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.98        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 8.82/8.98             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.98        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.82/8.98             sk_B)
% 8.82/8.98        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 8.82/8.98        | ~ (m1_subset_1 @ sk_C @ 
% 8.82/8.98             (k1_zfmisc_1 @ 
% 8.82/8.98              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.82/8.98        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.98        | ~ (v1_funct_1 @ sk_C)
% 8.82/8.98        | (v2_struct_0 @ sk_D)
% 8.82/8.98        | (v2_struct_0 @ sk_A))),
% 8.82/8.98      inference('sup-', [status(thm)], ['172', '187'])).
% 8.82/8.98  thf('189', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.98      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.98  thf('190', plain, ((v2_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('191', plain, ((l1_pre_topc @ sk_B)),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('192', plain,
% 8.82/8.98      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.98         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.98      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.98  thf('193', plain,
% 8.82/8.98      ((m1_subset_1 @ sk_C @ 
% 8.82/8.98        (k1_zfmisc_1 @ 
% 8.82/8.98         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('194', plain,
% 8.82/8.98      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/8.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.98  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('196', plain,
% 8.82/8.99      (((v2_struct_0 @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.99        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 8.82/8.99             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.99        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.82/8.99             sk_B)
% 8.82/8.99        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.82/8.99           sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_A))),
% 8.82/8.99      inference('demod', [status(thm)],
% 8.82/8.99                ['188', '189', '190', '191', '192', '193', '194', '195'])).
% 8.82/8.99  thf('197', plain,
% 8.82/8.99      ((~ (l1_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.82/8.99           sk_B)
% 8.82/8.99        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.82/8.99             sk_B)
% 8.82/8.99        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_B))),
% 8.82/8.99      inference('sup-', [status(thm)], ['171', '196'])).
% 8.82/8.99  thf('198', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.99      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.99  thf('199', plain,
% 8.82/8.99      (((v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.82/8.99           sk_B)
% 8.82/8.99        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 8.82/8.99             sk_B)
% 8.82/8.99        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_B))),
% 8.82/8.99      inference('demod', [status(thm)], ['197', '198'])).
% 8.82/8.99  thf('200', plain,
% 8.82/8.99      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.99        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.82/8.99           sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_A))),
% 8.82/8.99      inference('sup-', [status(thm)], ['170', '199'])).
% 8.82/8.99  thf('201', plain,
% 8.82/8.99      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)
% 8.82/8.99        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 8.82/8.99        | (v2_struct_0 @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.99      inference('simplify', [status(thm)], ['200'])).
% 8.82/8.99  thf('202', plain,
% 8.82/8.99      ((~ (l1_struct_0 @ sk_A)
% 8.82/8.99        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_B)
% 8.82/8.99        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.82/8.99           sk_B))),
% 8.82/8.99      inference('sup-', [status(thm)], ['169', '201'])).
% 8.82/8.99  thf('203', plain, ((l1_struct_0 @ sk_A)),
% 8.82/8.99      inference('sup-', [status(thm)], ['59', '60'])).
% 8.82/8.99  thf('204', plain,
% 8.82/8.99      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_B)
% 8.82/8.99        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.82/8.99           sk_B))),
% 8.82/8.99      inference('demod', [status(thm)], ['202', '203'])).
% 8.82/8.99  thf('205', plain,
% 8.82/8.99      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.82/8.99          sk_B)
% 8.82/8.99         | (v2_struct_0 @ sk_B)
% 8.82/8.99         | (v2_struct_0 @ sk_D)
% 8.82/8.99         | (v2_struct_0 @ sk_A)
% 8.82/8.99         | (v2_struct_0 @ sk_E))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.99      inference('sup-', [status(thm)], ['168', '204'])).
% 8.82/8.99  thf('206', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('207', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 8.82/8.99        | (v1_funct_1 @ sk_C))),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('208', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 8.82/8.99         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('split', [status(esa)], ['207'])).
% 8.82/8.99  thf('209', plain,
% 8.82/8.99      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 8.82/8.99         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('sup+', [status(thm)], ['206', '208'])).
% 8.82/8.99  thf('210', plain,
% 8.82/8.99      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.82/8.99           (k1_zfmisc_1 @ 
% 8.82/8.99            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 8.82/8.99        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99             sk_B)
% 8.82/8.99        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.82/8.99             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 8.82/8.99        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 8.82/8.99        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.82/8.99             (k1_zfmisc_1 @ 
% 8.82/8.99              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 8.82/8.99        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 8.82/8.99             sk_B)
% 8.82/8.99        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 8.82/8.99             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 8.82/8.99        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 8.82/8.99        | ~ (m1_subset_1 @ sk_C @ 
% 8.82/8.99             (k1_zfmisc_1 @ 
% 8.82/8.99              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.82/8.99        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.99        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.82/8.99        | ~ (v1_funct_1 @ sk_C))),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('211', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('212', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('213', plain,
% 8.82/8.99      (![X0 : $i]:
% 8.82/8.99         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.99           (k1_zfmisc_1 @ 
% 8.82/8.99            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/8.99          | ~ (l1_struct_0 @ X0))),
% 8.82/8.99      inference('demod', [status(thm)], ['58', '61', '64', '65', '66'])).
% 8.82/8.99  thf('214', plain,
% 8.82/8.99      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.82/8.99         (k1_zfmisc_1 @ 
% 8.82/8.99          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 8.82/8.99        | ~ (l1_struct_0 @ sk_E))),
% 8.82/8.99      inference('sup+', [status(thm)], ['212', '213'])).
% 8.82/8.99  thf('215', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('216', plain,
% 8.82/8.99      (![X14 : $i, X15 : $i]:
% 8.82/8.99         (~ (m1_pre_topc @ X14 @ X15)
% 8.82/8.99          | (l1_pre_topc @ X14)
% 8.82/8.99          | ~ (l1_pre_topc @ X15))),
% 8.82/8.99      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 8.82/8.99  thf('217', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_E))),
% 8.82/8.99      inference('sup-', [status(thm)], ['215', '216'])).
% 8.82/8.99  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('219', plain, ((l1_pre_topc @ sk_E)),
% 8.82/8.99      inference('demod', [status(thm)], ['217', '218'])).
% 8.82/8.99  thf('220', plain,
% 8.82/8.99      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 8.82/8.99      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.82/8.99  thf('221', plain, ((l1_struct_0 @ sk_E)),
% 8.82/8.99      inference('sup-', [status(thm)], ['219', '220'])).
% 8.82/8.99  thf('222', plain,
% 8.82/8.99      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.82/8.99        (k1_zfmisc_1 @ 
% 8.82/8.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.99      inference('demod', [status(thm)], ['214', '221'])).
% 8.82/8.99  thf('223', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('224', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('225', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('226', plain,
% 8.82/8.99      (![X0 : $i]:
% 8.82/8.99         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.99           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/8.99          | ~ (l1_struct_0 @ X0))),
% 8.82/8.99      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 8.82/8.99  thf('227', plain,
% 8.82/8.99      (((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.82/8.99         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 8.82/8.99        | ~ (l1_struct_0 @ sk_E))),
% 8.82/8.99      inference('sup+', [status(thm)], ['225', '226'])).
% 8.82/8.99  thf('228', plain, ((l1_struct_0 @ sk_E)),
% 8.82/8.99      inference('sup-', [status(thm)], ['219', '220'])).
% 8.82/8.99  thf('229', plain,
% 8.82/8.99      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.82/8.99        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 8.82/8.99      inference('demod', [status(thm)], ['227', '228'])).
% 8.82/8.99  thf('230', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('231', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('232', plain,
% 8.82/8.99      (![X0 : $i]:
% 8.82/8.99         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/8.99          | ~ (l1_struct_0 @ X0))),
% 8.82/8.99      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 8.82/8.99  thf('233', plain,
% 8.82/8.99      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 8.82/8.99        | ~ (l1_struct_0 @ sk_E))),
% 8.82/8.99      inference('sup+', [status(thm)], ['231', '232'])).
% 8.82/8.99  thf('234', plain, ((l1_struct_0 @ sk_E)),
% 8.82/8.99      inference('sup-', [status(thm)], ['219', '220'])).
% 8.82/8.99  thf('235', plain,
% 8.82/8.99      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('demod', [status(thm)], ['233', '234'])).
% 8.82/8.99  thf('236', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.99      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.99  thf('237', plain,
% 8.82/8.99      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.99        (k1_zfmisc_1 @ 
% 8.82/8.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.99      inference('demod', [status(thm)], ['68', '75'])).
% 8.82/8.99  thf('238', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.99      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.99  thf('239', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.99      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.99  thf('240', plain,
% 8.82/8.99      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.99        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 8.82/8.99      inference('demod', [status(thm)], ['94', '95'])).
% 8.82/8.99  thf('241', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.99      inference('clc', [status(thm)], ['50', '51'])).
% 8.82/8.99  thf('242', plain,
% 8.82/8.99      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 8.82/8.99      inference('demod', [status(thm)], ['107', '108'])).
% 8.82/8.99  thf('243', plain,
% 8.82/8.99      ((m1_subset_1 @ sk_C @ 
% 8.82/8.99        (k1_zfmisc_1 @ 
% 8.82/8.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('244', plain,
% 8.82/8.99      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('246', plain,
% 8.82/8.99      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 8.82/8.99           sk_B)
% 8.82/8.99        | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 8.82/8.99             sk_B)
% 8.82/8.99        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.99      inference('demod', [status(thm)],
% 8.82/8.99                ['210', '211', '222', '223', '224', '229', '230', '235', 
% 8.82/8.99                 '236', '237', '238', '239', '240', '241', '242', '243', 
% 8.82/8.99                 '244', '245'])).
% 8.82/8.99  thf('247', plain,
% 8.82/8.99      (((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.99         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 8.82/8.99              sk_D @ sk_B)))
% 8.82/8.99         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('sup-', [status(thm)], ['209', '246'])).
% 8.82/8.99  thf('248', plain,
% 8.82/8.99      ((((v2_struct_0 @ sk_E)
% 8.82/8.99         | (v2_struct_0 @ sk_A)
% 8.82/8.99         | (v2_struct_0 @ sk_D)
% 8.82/8.99         | (v2_struct_0 @ sk_B)
% 8.82/8.99         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 8.82/8.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.82/8.99             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('sup-', [status(thm)], ['205', '247'])).
% 8.82/8.99  thf('249', plain,
% 8.82/8.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 8.82/8.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.99      inference('split', [status(esa)], ['117'])).
% 8.82/8.99  thf('250', plain,
% 8.82/8.99      ((((v2_struct_0 @ sk_E)
% 8.82/8.99         | (v2_struct_0 @ sk_A)
% 8.82/8.99         | (v2_struct_0 @ sk_D)
% 8.82/8.99         | (v2_struct_0 @ sk_B)))
% 8.82/8.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.82/8.99             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('demod', [status(thm)], ['248', '249'])).
% 8.82/8.99  thf('251', plain, (~ (v2_struct_0 @ sk_B)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('252', plain,
% 8.82/8.99      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 8.82/8.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.82/8.99             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('sup-', [status(thm)], ['250', '251'])).
% 8.82/8.99  thf('253', plain, (~ (v2_struct_0 @ sk_D)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('254', plain,
% 8.82/8.99      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 8.82/8.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.82/8.99             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('clc', [status(thm)], ['252', '253'])).
% 8.82/8.99  thf('255', plain, (~ (v2_struct_0 @ sk_E)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('256', plain,
% 8.82/8.99      (((v2_struct_0 @ sk_A))
% 8.82/8.99         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 8.82/8.99             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('clc', [status(thm)], ['254', '255'])).
% 8.82/8.99  thf('257', plain, (~ (v2_struct_0 @ sk_A)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('258', plain,
% 8.82/8.99      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 8.82/8.99       ~
% 8.82/8.99       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 8.82/8.99      inference('sup-', [status(thm)], ['256', '257'])).
% 8.82/8.99  thf('259', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 8.82/8.99        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('260', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 8.82/8.99       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.99      inference('split', [status(esa)], ['259'])).
% 8.82/8.99  thf('261', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 8.82/8.99      inference('sat_resolution*', [status(thm)], ['167', '258', '260'])).
% 8.82/8.99  thf('262', plain,
% 8.82/8.99      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)),
% 8.82/8.99      inference('simpl_trail', [status(thm)], ['116', '261'])).
% 8.82/8.99  thf('263', plain,
% 8.82/8.99      (![X0 : $i]:
% 8.82/8.99         ((v2_struct_0 @ sk_A)
% 8.82/8.99          | (v2_struct_0 @ sk_D)
% 8.82/8.99          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 8.82/8.99          | (v5_pre_topc @ 
% 8.82/8.99             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 8.82/8.99             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 8.82/8.99          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.99               (k1_zfmisc_1 @ 
% 8.82/8.99                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 8.82/8.99          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 8.82/8.99          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 8.82/8.99               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 8.82/8.99          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 8.82/8.99          | ~ (m1_pre_topc @ X0 @ sk_A)
% 8.82/8.99          | (v2_struct_0 @ X0)
% 8.82/8.99          | (v2_struct_0 @ sk_B))),
% 8.82/8.99      inference('demod', [status(thm)], ['112', '262'])).
% 8.82/8.99  thf('264', plain,
% 8.82/8.99      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.82/8.99           (k1_zfmisc_1 @ 
% 8.82/8.99            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 8.82/8.99        | (v2_struct_0 @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 8.82/8.99        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 8.82/8.99        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 8.82/8.99             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 8.82/8.99        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99             sk_B)
% 8.82/8.99        | (v5_pre_topc @ 
% 8.82/8.99           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 8.82/8.99           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 8.82/8.99        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_A))),
% 8.82/8.99      inference('sup-', [status(thm)], ['45', '263'])).
% 8.82/8.99  thf('265', plain,
% 8.82/8.99      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.82/8.99        (k1_zfmisc_1 @ 
% 8.82/8.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 8.82/8.99      inference('demod', [status(thm)], ['214', '221'])).
% 8.82/8.99  thf('266', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('267', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('268', plain,
% 8.82/8.99      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('demod', [status(thm)], ['233', '234'])).
% 8.82/8.99  thf('269', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('270', plain,
% 8.82/8.99      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 8.82/8.99        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 8.82/8.99      inference('demod', [status(thm)], ['227', '228'])).
% 8.82/8.99  thf('271', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('272', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 8.82/8.99         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('split', [status(esa)], ['207'])).
% 8.82/8.99  thf('273', plain,
% 8.82/8.99      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 8.82/8.99         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 8.82/8.99      inference('clc', [status(thm)], ['43', '44'])).
% 8.82/8.99  thf('274', plain,
% 8.82/8.99      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 8.82/8.99         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 8.82/8.99               sk_B)))),
% 8.82/8.99      inference('demod', [status(thm)], ['272', '273'])).
% 8.82/8.99  thf('275', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 8.82/8.99        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('276', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 8.82/8.99       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.99      inference('split', [status(esa)], ['275'])).
% 8.82/8.99  thf('277', plain,
% 8.82/8.99      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 8.82/8.99      inference('sat_resolution*', [status(thm)], ['167', '258', '276'])).
% 8.82/8.99  thf('278', plain,
% 8.82/8.99      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)),
% 8.82/8.99      inference('simpl_trail', [status(thm)], ['274', '277'])).
% 8.82/8.99  thf('279', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('280', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('281', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('282', plain,
% 8.82/8.99      (((v2_struct_0 @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_A))),
% 8.82/8.99      inference('demod', [status(thm)],
% 8.82/8.99                ['264', '265', '266', '267', '268', '269', '270', '271', 
% 8.82/8.99                 '278', '279', '280', '281'])).
% 8.82/8.99  thf('283', plain,
% 8.82/8.99      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_B))),
% 8.82/8.99      inference('sup+', [status(thm)], ['38', '282'])).
% 8.82/8.99  thf('284', plain,
% 8.82/8.99      (((v2_struct_0 @ sk_B)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_E)
% 8.82/8.99        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.99      inference('simplify', [status(thm)], ['283'])).
% 8.82/8.99  thf('285', plain,
% 8.82/8.99      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 8.82/8.99         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 8.82/8.99      inference('split', [status(esa)], ['156'])).
% 8.82/8.99  thf('286', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 8.82/8.99      inference('sat_resolution*', [status(thm)], ['167', '258'])).
% 8.82/8.99  thf('287', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 8.82/8.99      inference('simpl_trail', [status(thm)], ['285', '286'])).
% 8.82/8.99  thf('288', plain,
% 8.82/8.99      (((v2_struct_0 @ sk_E)
% 8.82/8.99        | (v2_struct_0 @ sk_A)
% 8.82/8.99        | (v2_struct_0 @ sk_D)
% 8.82/8.99        | (v2_struct_0 @ sk_B))),
% 8.82/8.99      inference('sup-', [status(thm)], ['284', '287'])).
% 8.82/8.99  thf('289', plain, (~ (v2_struct_0 @ sk_B)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('290', plain,
% 8.82/8.99      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E))),
% 8.82/8.99      inference('sup-', [status(thm)], ['288', '289'])).
% 8.82/8.99  thf('291', plain, (~ (v2_struct_0 @ sk_D)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('292', plain, (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A))),
% 8.82/8.99      inference('clc', [status(thm)], ['290', '291'])).
% 8.82/8.99  thf('293', plain, (~ (v2_struct_0 @ sk_E)),
% 8.82/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.82/8.99  thf('294', plain, ((v2_struct_0 @ sk_A)),
% 8.82/8.99      inference('clc', [status(thm)], ['292', '293'])).
% 8.82/8.99  thf('295', plain, ($false), inference('demod', [status(thm)], ['0', '294'])).
% 8.82/8.99  
% 8.82/8.99  % SZS output end Refutation
% 8.82/8.99  
% 8.82/8.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
