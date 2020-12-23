%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.04S8U1zMhH

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:07 EST 2020

% Result     : Theorem 20.41s
% Output     : Refutation 20.41s
% Verified   : 
% Statistics : Number of formulae       :  338 (6079 expanded)
%              Number of leaves         :   40 (1819 expanded)
%              Depth                    :   34
%              Number of atoms          : 4592 (429835 expanded)
%              Number of equality atoms :   68 (3712 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( v2_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X22 @ X21 @ X23 ) @ X22 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( k2_tmap_1 @ X19 @ X17 @ X20 @ X18 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) @ X20 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( v1_funct_2 @ X20 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 )
        = ( k7_relat_1 @ X10 @ X13 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( ( k7_relat_1 @ X2 @ X3 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['31','32'])).

thf('38',plain,
    ( ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','38'])).

thf('40',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

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

thf('55',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X32 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X32 ) @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X32 ) @ X32 @ X28 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X29 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X29 ) @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X29 ) @ X29 @ X28 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( r4_tsep_1 @ X30 @ X32 @ X29 )
      | ~ ( m1_pre_topc @ X32 @ X30 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('56',plain,(
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
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_struct_0 @ X27 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X25 @ X26 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('62',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63','66','67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['57','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('86',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('87',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X25 @ X26 @ X24 @ X27 ) @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('92',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['87','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('98',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('100',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X25 @ X26 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['100','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['75','76'])).

thf('111',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
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
    inference(demod,[status(thm)],['56','78','79','80','81','82','83','84','85','86','98','99','111','112','113'])).

thf('115',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['115'])).

thf('117',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('118',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('122',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['39'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('124',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63','66','67','68'])).

thf('126',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X29 ) @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( r4_tsep_1 @ X30 @ X32 @ X29 )
      | ~ ( m1_pre_topc @ X32 @ X30 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('127',plain,(
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
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
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
    inference(demod,[status(thm)],['127','128','129','130','131','132','133','134'])).

thf('136',plain,
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
    inference('sup-',[status(thm)],['124','135'])).

thf('137',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('143',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('147',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138','139','140','141','142','143','144','145','146'])).

thf('148',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
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
    inference('sup-',[status(thm)],['122','150'])).

thf('152',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['121','152'])).

thf('154',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('155',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['120','155'])).

thf('157',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('158',plain,
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

thf('159',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['158'])).

thf('160',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['157','159'])).

thf('161',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['119'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('172',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['39'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('174',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63','66','67','68'])).

thf('176',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X30 @ X32 @ X29 ) ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X30 @ X28 @ X31 @ X32 ) @ X32 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( r4_tsep_1 @ X30 @ X32 @ X29 )
      | ~ ( m1_pre_topc @ X32 @ X30 )
      | ( v2_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('177',plain,(
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
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X1 @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( r4_tsep_1 @ sk_A @ X1 @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1 ) @ X1 @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ X1 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['177','178','179','180','181','182','183','184'])).

thf('186',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( m1_pre_topc @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( r4_tsep_1 @ sk_A @ sk_D @ sk_E )
    | ~ ( m1_pre_topc @ sk_D @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['174','185'])).

thf('187',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('193',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('197',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188','189','190','191','192','193','194','195','196'])).

thf('198',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['173','197'])).

thf('199',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
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
    inference('sup-',[status(thm)],['172','200'])).

thf('202',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['201'])).

thf('203',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['171','202'])).

thf('204',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('205',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['170','205'])).

thf('207',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('208',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['208'])).

thf('210',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup+',[status(thm)],['207','209'])).

thf('211',plain,
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

thf('212',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('213',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','63','66','67','68'])).

thf('215',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('218',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('222',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['215','222'])).

thf('224',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('225',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('226',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('228',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['220','221'])).

thf('230',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('232',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('234',plain,
    ( ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ~ ( l1_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['232','233'])).

thf('235',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['220','221'])).

thf('236',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('238',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','77'])).

thf('239',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('240',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('241',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('242',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('243',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('244',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['211','212','223','224','225','230','231','236','237','238','239','240','241','242','243','244','245','246'])).

thf('248',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['210','247'])).

thf('249',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['206','248'])).

thf('250',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['119'])).

thf('251',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['253','254'])).

thf('256',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['255','256'])).

thf('258',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['260'])).

thf('262',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['169','259','261'])).

thf('263',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['118','262'])).

thf('264',plain,(
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
    inference(demod,[status(thm)],['114','263'])).

thf('265',plain,
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
    inference('sup-',[status(thm)],['47','264'])).

thf('266',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['215','222'])).

thf('267',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('269',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('270',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('271',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('272',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('273',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['208'])).

thf('274',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('275',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('277',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['276'])).

thf('278',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['169','259','277'])).

thf('279',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['275','278'])).

thf('280',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['265','266','267','268','269','270','271','272','279','280','281','282'])).

thf('284',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','283'])).

thf('285',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['284'])).

thf('286',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['158'])).

thf('287',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['169','259'])).

thf('288',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['286','287'])).

thf('289',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['285','288'])).

thf('290',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['289','290'])).

thf('292',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['291','292'])).

thf('294',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('295',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['293','294'])).

thf('296',plain,(
    $false ),
    inference(demod,[status(thm)],['0','295'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.04S8U1zMhH
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:31:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 20.41/20.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.41/20.60  % Solved by: fo/fo7.sh
% 20.41/20.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.41/20.60  % done 4043 iterations in 20.130s
% 20.41/20.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.41/20.60  % SZS output start Refutation
% 20.41/20.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 20.41/20.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.41/20.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 20.41/20.60  thf(sk_B_type, type, sk_B: $i).
% 20.41/20.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 20.41/20.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 20.41/20.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 20.41/20.60  thf(sk_E_type, type, sk_E: $i).
% 20.41/20.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 20.41/20.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.41/20.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.41/20.60  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 20.41/20.60  thf(sk_A_type, type, sk_A: $i).
% 20.41/20.60  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 20.41/20.60  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 20.41/20.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 20.41/20.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.41/20.60  thf(sk_C_type, type, sk_C: $i).
% 20.41/20.60  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 20.41/20.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 20.41/20.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 20.41/20.60  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 20.41/20.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 20.41/20.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.41/20.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 20.41/20.60  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 20.41/20.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.41/20.60  thf(sk_D_type, type, sk_D: $i).
% 20.41/20.60  thf(t132_tmap_1, conjecture,
% 20.41/20.60    (![A:$i]:
% 20.41/20.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.41/20.60       ( ![B:$i]:
% 20.41/20.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 20.41/20.60             ( l1_pre_topc @ B ) ) =>
% 20.41/20.60           ( ![C:$i]:
% 20.41/20.60             ( ( ( v1_funct_1 @ C ) & 
% 20.41/20.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                 ( m1_subset_1 @
% 20.41/20.60                   C @ 
% 20.41/20.60                   ( k1_zfmisc_1 @
% 20.41/20.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 20.41/20.60               ( ![D:$i]:
% 20.41/20.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 20.41/20.60                   ( ![E:$i]:
% 20.41/20.60                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 20.41/20.60                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 20.41/20.60                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 20.41/20.60                         ( ( ( v1_funct_1 @ C ) & 
% 20.41/20.60                             ( v1_funct_2 @
% 20.41/20.60                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                             ( v5_pre_topc @ C @ A @ B ) & 
% 20.41/20.60                             ( m1_subset_1 @
% 20.41/20.60                               C @ 
% 20.41/20.60                               ( k1_zfmisc_1 @
% 20.41/20.60                                 ( k2_zfmisc_1 @
% 20.41/20.60                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 20.41/20.60                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 20.41/20.60                             ( v1_funct_2 @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.41/20.60                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                             ( v5_pre_topc @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 20.41/20.60                             ( m1_subset_1 @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.41/20.60                               ( k1_zfmisc_1 @
% 20.41/20.60                                 ( k2_zfmisc_1 @
% 20.41/20.60                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 20.41/20.60                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 20.41/20.60                             ( v1_funct_2 @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 20.41/20.60                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                             ( v5_pre_topc @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 20.41/20.60                             ( m1_subset_1 @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 20.41/20.60                               ( k1_zfmisc_1 @
% 20.41/20.60                                 ( k2_zfmisc_1 @
% 20.41/20.60                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 20.41/20.60  thf(zf_stmt_0, negated_conjecture,
% 20.41/20.60    (~( ![A:$i]:
% 20.41/20.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 20.41/20.60            ( l1_pre_topc @ A ) ) =>
% 20.41/20.60          ( ![B:$i]:
% 20.41/20.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 20.41/20.60                ( l1_pre_topc @ B ) ) =>
% 20.41/20.60              ( ![C:$i]:
% 20.41/20.60                ( ( ( v1_funct_1 @ C ) & 
% 20.41/20.60                    ( v1_funct_2 @
% 20.41/20.60                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                    ( m1_subset_1 @
% 20.41/20.60                      C @ 
% 20.41/20.60                      ( k1_zfmisc_1 @
% 20.41/20.60                        ( k2_zfmisc_1 @
% 20.41/20.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 20.41/20.60                  ( ![D:$i]:
% 20.41/20.60                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 20.41/20.60                      ( ![E:$i]:
% 20.41/20.60                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 20.41/20.60                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 20.41/20.60                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 20.41/20.60                            ( ( ( v1_funct_1 @ C ) & 
% 20.41/20.60                                ( v1_funct_2 @
% 20.41/20.60                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                                ( v5_pre_topc @ C @ A @ B ) & 
% 20.41/20.60                                ( m1_subset_1 @
% 20.41/20.60                                  C @ 
% 20.41/20.60                                  ( k1_zfmisc_1 @
% 20.41/20.60                                    ( k2_zfmisc_1 @
% 20.41/20.60                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 20.41/20.60                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 20.41/20.60                                ( v1_funct_2 @
% 20.41/20.60                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.41/20.60                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                                ( v5_pre_topc @
% 20.41/20.60                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 20.41/20.60                                ( m1_subset_1 @
% 20.41/20.60                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.41/20.60                                  ( k1_zfmisc_1 @
% 20.41/20.60                                    ( k2_zfmisc_1 @
% 20.41/20.60                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 20.41/20.60                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 20.41/20.60                                ( v1_funct_2 @
% 20.41/20.60                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 20.41/20.60                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                                ( v5_pre_topc @
% 20.41/20.60                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 20.41/20.60                                ( m1_subset_1 @
% 20.41/20.60                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 20.41/20.60                                  ( k1_zfmisc_1 @
% 20.41/20.60                                    ( k2_zfmisc_1 @
% 20.41/20.60                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 20.41/20.60    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 20.41/20.60  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf(dt_k1_tsep_1, axiom,
% 20.41/20.60    (![A:$i,B:$i,C:$i]:
% 20.41/20.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 20.41/20.60         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 20.41/20.60         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 20.41/20.60       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 20.41/20.60         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 20.41/20.60         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 20.41/20.60  thf('3', plain,
% 20.41/20.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 20.41/20.60         (~ (m1_pre_topc @ X21 @ X22)
% 20.41/20.60          | (v2_struct_0 @ X21)
% 20.41/20.60          | ~ (l1_pre_topc @ X22)
% 20.41/20.60          | (v2_struct_0 @ X22)
% 20.41/20.60          | (v2_struct_0 @ X23)
% 20.41/20.60          | ~ (m1_pre_topc @ X23 @ X22)
% 20.41/20.60          | (m1_pre_topc @ (k1_tsep_1 @ X22 @ X21 @ X23) @ X22))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 20.41/20.60  thf('4', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | (v2_struct_0 @ sk_A)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ sk_D))),
% 20.41/20.60      inference('sup-', [status(thm)], ['2', '3'])).
% 20.41/20.60  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('6', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | (v2_struct_0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ sk_D))),
% 20.41/20.60      inference('demod', [status(thm)], ['4', '5'])).
% 20.41/20.60  thf('7', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_A))),
% 20.41/20.60      inference('sup-', [status(thm)], ['1', '6'])).
% 20.41/20.60  thf('8', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('9', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (m1_pre_topc @ sk_A @ sk_A))),
% 20.41/20.60      inference('demod', [status(thm)], ['7', '8'])).
% 20.41/20.60  thf('10', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf(d4_tmap_1, axiom,
% 20.41/20.60    (![A:$i]:
% 20.41/20.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.41/20.60       ( ![B:$i]:
% 20.41/20.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 20.41/20.60             ( l1_pre_topc @ B ) ) =>
% 20.41/20.60           ( ![C:$i]:
% 20.41/20.60             ( ( ( v1_funct_1 @ C ) & 
% 20.41/20.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                 ( m1_subset_1 @
% 20.41/20.60                   C @ 
% 20.41/20.60                   ( k1_zfmisc_1 @
% 20.41/20.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 20.41/20.60               ( ![D:$i]:
% 20.41/20.60                 ( ( m1_pre_topc @ D @ A ) =>
% 20.41/20.60                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 20.41/20.60                     ( k2_partfun1 @
% 20.41/20.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 20.41/20.60                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 20.41/20.60  thf('11', plain,
% 20.41/20.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 20.41/20.60         ((v2_struct_0 @ X17)
% 20.41/20.60          | ~ (v2_pre_topc @ X17)
% 20.41/20.60          | ~ (l1_pre_topc @ X17)
% 20.41/20.60          | ~ (m1_pre_topc @ X18 @ X19)
% 20.41/20.60          | ((k2_tmap_1 @ X19 @ X17 @ X20 @ X18)
% 20.41/20.60              = (k2_partfun1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17) @ 
% 20.41/20.60                 X20 @ (u1_struct_0 @ X18)))
% 20.41/20.60          | ~ (m1_subset_1 @ X20 @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))))
% 20.41/20.60          | ~ (v1_funct_2 @ X20 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X17))
% 20.41/20.60          | ~ (v1_funct_1 @ X20)
% 20.41/20.60          | ~ (l1_pre_topc @ X19)
% 20.41/20.60          | ~ (v2_pre_topc @ X19)
% 20.41/20.60          | (v2_struct_0 @ X19))),
% 20.41/20.60      inference('cnf', [status(esa)], [d4_tmap_1])).
% 20.41/20.60  thf('12', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v2_struct_0 @ sk_A)
% 20.41/20.60          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.60          | ~ (v1_funct_1 @ sk_C)
% 20.41/20.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 20.41/20.60              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 20.41/20.60                 sk_C @ (u1_struct_0 @ X0)))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_B)
% 20.41/20.60          | ~ (v2_pre_topc @ sk_B)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['10', '11'])).
% 20.41/20.60  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('16', plain,
% 20.41/20.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('17', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf(redefinition_k2_partfun1, axiom,
% 20.41/20.60    (![A:$i,B:$i,C:$i,D:$i]:
% 20.41/20.60     ( ( ( v1_funct_1 @ C ) & 
% 20.41/20.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.41/20.60       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 20.41/20.60  thf('18', plain,
% 20.41/20.60      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 20.41/20.60         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 20.41/20.60          | ~ (v1_funct_1 @ X10)
% 20.41/20.60          | ((k2_partfun1 @ X11 @ X12 @ X10 @ X13) = (k7_relat_1 @ X10 @ X13)))),
% 20.41/20.60      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 20.41/20.60  thf('19', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 20.41/20.60            X0) = (k7_relat_1 @ sk_C @ X0))
% 20.41/20.60          | ~ (v1_funct_1 @ sk_C))),
% 20.41/20.60      inference('sup-', [status(thm)], ['17', '18'])).
% 20.41/20.60  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('21', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 20.41/20.60           X0) = (k7_relat_1 @ sk_C @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['19', '20'])).
% 20.41/20.60  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('24', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v2_struct_0 @ sk_A)
% 20.41/20.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 20.41/20.60              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 20.41/20.60  thf('25', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 20.41/20.60            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('sup-', [status(thm)], ['9', '24'])).
% 20.41/20.60  thf('26', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf(cc2_relset_1, axiom,
% 20.41/20.60    (![A:$i,B:$i,C:$i]:
% 20.41/20.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.41/20.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 20.41/20.60  thf('27', plain,
% 20.41/20.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 20.41/20.60         ((v4_relat_1 @ X7 @ X8)
% 20.41/20.60          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 20.41/20.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 20.41/20.60  thf('28', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 20.41/20.60      inference('sup-', [status(thm)], ['26', '27'])).
% 20.41/20.60  thf(d18_relat_1, axiom,
% 20.41/20.60    (![A:$i,B:$i]:
% 20.41/20.60     ( ( v1_relat_1 @ B ) =>
% 20.41/20.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 20.41/20.60  thf('29', plain,
% 20.41/20.60      (![X0 : $i, X1 : $i]:
% 20.41/20.60         (~ (v4_relat_1 @ X0 @ X1)
% 20.41/20.60          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 20.41/20.60          | ~ (v1_relat_1 @ X0))),
% 20.41/20.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 20.41/20.60  thf('30', plain,
% 20.41/20.60      ((~ (v1_relat_1 @ sk_C)
% 20.41/20.60        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['28', '29'])).
% 20.41/20.60  thf('31', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf(cc1_relset_1, axiom,
% 20.41/20.60    (![A:$i,B:$i,C:$i]:
% 20.41/20.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.41/20.60       ( v1_relat_1 @ C ) ))).
% 20.41/20.60  thf('32', plain,
% 20.41/20.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 20.41/20.60         ((v1_relat_1 @ X4)
% 20.41/20.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 20.41/20.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 20.41/20.60  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 20.41/20.60      inference('sup-', [status(thm)], ['31', '32'])).
% 20.41/20.60  thf('34', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 20.41/20.60      inference('demod', [status(thm)], ['30', '33'])).
% 20.41/20.60  thf(t97_relat_1, axiom,
% 20.41/20.60    (![A:$i,B:$i]:
% 20.41/20.60     ( ( v1_relat_1 @ B ) =>
% 20.41/20.60       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 20.41/20.60         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 20.41/20.60  thf('35', plain,
% 20.41/20.60      (![X2 : $i, X3 : $i]:
% 20.41/20.60         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 20.41/20.60          | ((k7_relat_1 @ X2 @ X3) = (X2))
% 20.41/20.60          | ~ (v1_relat_1 @ X2))),
% 20.41/20.60      inference('cnf', [status(esa)], [t97_relat_1])).
% 20.41/20.60  thf('36', plain,
% 20.41/20.60      ((~ (v1_relat_1 @ sk_C)
% 20.41/20.60        | ((k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['34', '35'])).
% 20.41/20.60  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 20.41/20.60      inference('sup-', [status(thm)], ['31', '32'])).
% 20.41/20.60  thf('38', plain, (((k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 20.41/20.60      inference('demod', [status(thm)], ['36', '37'])).
% 20.41/20.60  thf('39', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('demod', [status(thm)], ['25', '38'])).
% 20.41/20.60  thf('40', plain,
% 20.41/20.60      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_E))),
% 20.41/20.60      inference('simplify', [status(thm)], ['39'])).
% 20.41/20.60  thf('41', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('42', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v2_struct_0 @ sk_A)
% 20.41/20.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 20.41/20.60              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 20.41/20.60  thf('43', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_B)
% 20.41/20.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('sup-', [status(thm)], ['41', '42'])).
% 20.41/20.60  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('45', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_A)
% 20.41/20.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))),
% 20.41/20.60      inference('clc', [status(thm)], ['43', '44'])).
% 20.41/20.60  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('47', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('48', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('49', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v2_struct_0 @ sk_A)
% 20.41/20.60          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 20.41/20.60              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 20.41/20.60  thf('50', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_B)
% 20.41/20.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('sup-', [status(thm)], ['48', '49'])).
% 20.41/20.60  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('52', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_A)
% 20.41/20.60        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))),
% 20.41/20.60      inference('clc', [status(thm)], ['50', '51'])).
% 20.41/20.60  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('54', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf(t129_tmap_1, axiom,
% 20.41/20.60    (![A:$i]:
% 20.41/20.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.41/20.60       ( ![B:$i]:
% 20.41/20.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 20.41/20.60             ( l1_pre_topc @ B ) ) =>
% 20.41/20.60           ( ![C:$i]:
% 20.41/20.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 20.41/20.60               ( ![D:$i]:
% 20.41/20.60                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 20.41/20.60                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 20.41/20.60                     ( ![E:$i]:
% 20.41/20.60                       ( ( ( v1_funct_1 @ E ) & 
% 20.41/20.60                           ( v1_funct_2 @
% 20.41/20.60                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                           ( m1_subset_1 @
% 20.41/20.60                             E @ 
% 20.41/20.60                             ( k1_zfmisc_1 @
% 20.41/20.60                               ( k2_zfmisc_1 @
% 20.41/20.60                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 20.41/20.60                         ( ( ( v1_funct_1 @
% 20.41/20.60                               ( k2_tmap_1 @
% 20.41/20.60                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 20.41/20.60                             ( v1_funct_2 @
% 20.41/20.60                               ( k2_tmap_1 @
% 20.41/20.60                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.41/20.60                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.41/20.60                               ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                             ( v5_pre_topc @
% 20.41/20.60                               ( k2_tmap_1 @
% 20.41/20.60                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.41/20.60                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 20.41/20.60                             ( m1_subset_1 @
% 20.41/20.60                               ( k2_tmap_1 @
% 20.41/20.60                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.41/20.60                               ( k1_zfmisc_1 @
% 20.41/20.60                                 ( k2_zfmisc_1 @
% 20.41/20.60                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.41/20.60                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 20.41/20.60                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 20.41/20.60                             ( v1_funct_2 @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 20.41/20.60                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                             ( v5_pre_topc @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 20.41/20.60                             ( m1_subset_1 @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 20.41/20.60                               ( k1_zfmisc_1 @
% 20.41/20.60                                 ( k2_zfmisc_1 @
% 20.41/20.60                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 20.41/20.60                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 20.41/20.60                             ( v1_funct_2 @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 20.41/20.60                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60                             ( v5_pre_topc @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 20.41/20.60                             ( m1_subset_1 @
% 20.41/20.60                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 20.41/20.60                               ( k1_zfmisc_1 @
% 20.41/20.60                                 ( k2_zfmisc_1 @
% 20.41/20.60                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 20.41/20.60  thf('55', plain,
% 20.41/20.60      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 20.41/20.60         ((v2_struct_0 @ X28)
% 20.41/20.60          | ~ (v2_pre_topc @ X28)
% 20.41/20.60          | ~ (l1_pre_topc @ X28)
% 20.41/20.60          | (v2_struct_0 @ X29)
% 20.41/20.60          | ~ (m1_pre_topc @ X29 @ X30)
% 20.41/20.60          | ~ (v1_funct_1 @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X32))
% 20.41/20.60          | ~ (v1_funct_2 @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X32) @ 
% 20.41/20.60               (u1_struct_0 @ X32) @ (u1_struct_0 @ X28))
% 20.41/20.60          | ~ (v5_pre_topc @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X32) @ X32 @ X28)
% 20.41/20.60          | ~ (m1_subset_1 @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X32) @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X28))))
% 20.41/20.60          | ~ (v1_funct_1 @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X29))
% 20.41/20.60          | ~ (v1_funct_2 @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X29) @ 
% 20.41/20.60               (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 20.41/20.60          | ~ (v5_pre_topc @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X29) @ X29 @ X28)
% 20.41/20.60          | ~ (m1_subset_1 @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X29) @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 20.41/20.60          | (v5_pre_topc @ 
% 20.41/20.60             (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60             (k1_tsep_1 @ X30 @ X32 @ X29) @ X28)
% 20.41/20.60          | ~ (m1_subset_1 @ X31 @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))))
% 20.41/20.60          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))
% 20.41/20.60          | ~ (v1_funct_1 @ X31)
% 20.41/20.60          | ~ (r4_tsep_1 @ X30 @ X32 @ X29)
% 20.41/20.60          | ~ (m1_pre_topc @ X32 @ X30)
% 20.41/20.60          | (v2_struct_0 @ X32)
% 20.41/20.60          | ~ (l1_pre_topc @ X30)
% 20.41/20.60          | ~ (v2_pre_topc @ X30)
% 20.41/20.60          | (v2_struct_0 @ X30))),
% 20.41/20.60      inference('cnf', [status(esa)], [t129_tmap_1])).
% 20.41/20.60  thf('56', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         (~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | (v2_struct_0 @ sk_A)
% 20.41/20.60          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ sk_D)
% 20.41/20.60          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 20.41/20.60          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 20.41/20.60          | ~ (v1_funct_1 @ sk_C)
% 20.41/20.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (m1_subset_1 @ sk_C @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | (v5_pre_topc @ 
% 20.41/20.60             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 20.41/20.60             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 20.41/20.60          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 20.41/20.60          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.41/20.60          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.41/20.60               sk_B)
% 20.41/20.60          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.41/20.60               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_B)
% 20.41/20.60          | ~ (v2_pre_topc @ sk_B)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['54', '55'])).
% 20.41/20.60  thf('57', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('58', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf(dt_k2_tmap_1, axiom,
% 20.41/20.60    (![A:$i,B:$i,C:$i,D:$i]:
% 20.41/20.60     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 20.41/20.60         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.41/20.60         ( m1_subset_1 @
% 20.41/20.60           C @ 
% 20.41/20.60           ( k1_zfmisc_1 @
% 20.41/20.60             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 20.41/20.60         ( l1_struct_0 @ D ) ) =>
% 20.41/20.60       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 20.41/20.60         ( v1_funct_2 @
% 20.41/20.60           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 20.41/20.60           ( u1_struct_0 @ B ) ) & 
% 20.41/20.60         ( m1_subset_1 @
% 20.41/20.60           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.41/20.60           ( k1_zfmisc_1 @
% 20.41/20.60             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 20.41/20.60  thf('59', plain,
% 20.41/20.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 20.41/20.60         (~ (m1_subset_1 @ X24 @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))))
% 20.41/20.60          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 20.41/20.60          | ~ (v1_funct_1 @ X24)
% 20.41/20.60          | ~ (l1_struct_0 @ X26)
% 20.41/20.60          | ~ (l1_struct_0 @ X25)
% 20.41/20.60          | ~ (l1_struct_0 @ X27)
% 20.41/20.60          | (m1_subset_1 @ (k2_tmap_1 @ X25 @ X26 @ X24 @ X27) @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26)))))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 20.41/20.60  thf('60', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (k1_zfmisc_1 @ 
% 20.41/20.60            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | ~ (l1_struct_0 @ X0)
% 20.41/20.60          | ~ (l1_struct_0 @ sk_A)
% 20.41/20.60          | ~ (l1_struct_0 @ sk_B)
% 20.41/20.60          | ~ (v1_funct_1 @ sk_C)
% 20.41/20.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['58', '59'])).
% 20.41/20.60  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf(dt_l1_pre_topc, axiom,
% 20.41/20.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 20.41/20.60  thf('62', plain,
% 20.41/20.60      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 20.41/20.60  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('64', plain, ((l1_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('65', plain,
% 20.41/20.60      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 20.41/20.60  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 20.41/20.60      inference('sup-', [status(thm)], ['64', '65'])).
% 20.41/20.60  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('68', plain,
% 20.41/20.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('69', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (k1_zfmisc_1 @ 
% 20.41/20.60            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['60', '63', '66', '67', '68'])).
% 20.41/20.60  thf('70', plain,
% 20.41/20.60      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60         (k1_zfmisc_1 @ 
% 20.41/20.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | ~ (l1_struct_0 @ sk_D))),
% 20.41/20.60      inference('sup+', [status(thm)], ['57', '69'])).
% 20.41/20.60  thf('71', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf(dt_m1_pre_topc, axiom,
% 20.41/20.60    (![A:$i]:
% 20.41/20.60     ( ( l1_pre_topc @ A ) =>
% 20.41/20.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 20.41/20.60  thf('72', plain,
% 20.41/20.60      (![X15 : $i, X16 : $i]:
% 20.41/20.60         (~ (m1_pre_topc @ X15 @ X16)
% 20.41/20.60          | (l1_pre_topc @ X15)
% 20.41/20.60          | ~ (l1_pre_topc @ X16))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 20.41/20.60  thf('73', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 20.41/20.60      inference('sup-', [status(thm)], ['71', '72'])).
% 20.41/20.60  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('75', plain, ((l1_pre_topc @ sk_D)),
% 20.41/20.60      inference('demod', [status(thm)], ['73', '74'])).
% 20.41/20.60  thf('76', plain,
% 20.41/20.60      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 20.41/20.60  thf('77', plain, ((l1_struct_0 @ sk_D)),
% 20.41/20.60      inference('sup-', [status(thm)], ['75', '76'])).
% 20.41/20.60  thf('78', plain,
% 20.41/20.60      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('demod', [status(thm)], ['70', '77'])).
% 20.41/20.60  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('83', plain,
% 20.41/20.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('84', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('85', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('86', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('87', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('88', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('89', plain,
% 20.41/20.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 20.41/20.60         (~ (m1_subset_1 @ X24 @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))))
% 20.41/20.60          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 20.41/20.60          | ~ (v1_funct_1 @ X24)
% 20.41/20.60          | ~ (l1_struct_0 @ X26)
% 20.41/20.60          | ~ (l1_struct_0 @ X25)
% 20.41/20.60          | ~ (l1_struct_0 @ X27)
% 20.41/20.60          | (v1_funct_2 @ (k2_tmap_1 @ X25 @ X26 @ X24 @ X27) @ 
% 20.41/20.60             (u1_struct_0 @ X27) @ (u1_struct_0 @ X26)))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 20.41/20.60  thf('90', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (l1_struct_0 @ X0)
% 20.41/20.60          | ~ (l1_struct_0 @ sk_A)
% 20.41/20.60          | ~ (l1_struct_0 @ sk_B)
% 20.41/20.60          | ~ (v1_funct_1 @ sk_C)
% 20.41/20.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['88', '89'])).
% 20.41/20.60  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('92', plain, ((l1_struct_0 @ sk_B)),
% 20.41/20.60      inference('sup-', [status(thm)], ['64', '65'])).
% 20.41/20.60  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('94', plain,
% 20.41/20.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('95', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 20.41/20.60  thf('96', plain,
% 20.41/20.60      (((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (l1_struct_0 @ sk_D))),
% 20.41/20.60      inference('sup+', [status(thm)], ['87', '95'])).
% 20.41/20.60  thf('97', plain, ((l1_struct_0 @ sk_D)),
% 20.41/20.60      inference('sup-', [status(thm)], ['75', '76'])).
% 20.41/20.60  thf('98', plain,
% 20.41/20.60      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['96', '97'])).
% 20.41/20.60  thf('99', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('100', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('101', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('102', plain,
% 20.41/20.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 20.41/20.60         (~ (m1_subset_1 @ X24 @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))))
% 20.41/20.60          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 20.41/20.60          | ~ (v1_funct_1 @ X24)
% 20.41/20.60          | ~ (l1_struct_0 @ X26)
% 20.41/20.60          | ~ (l1_struct_0 @ X25)
% 20.41/20.60          | ~ (l1_struct_0 @ X27)
% 20.41/20.60          | (v1_funct_1 @ (k2_tmap_1 @ X25 @ X26 @ X24 @ X27)))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 20.41/20.60  thf('103', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.41/20.60          | ~ (l1_struct_0 @ X0)
% 20.41/20.60          | ~ (l1_struct_0 @ sk_A)
% 20.41/20.60          | ~ (l1_struct_0 @ sk_B)
% 20.41/20.60          | ~ (v1_funct_1 @ sk_C)
% 20.41/20.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['101', '102'])).
% 20.41/20.60  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 20.41/20.60      inference('sup-', [status(thm)], ['64', '65'])).
% 20.41/20.60  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('107', plain,
% 20.41/20.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('108', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 20.41/20.60  thf('109', plain,
% 20.41/20.60      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 20.41/20.60        | ~ (l1_struct_0 @ sk_D))),
% 20.41/20.60      inference('sup+', [status(thm)], ['100', '108'])).
% 20.41/20.60  thf('110', plain, ((l1_struct_0 @ sk_D)),
% 20.41/20.60      inference('sup-', [status(thm)], ['75', '76'])).
% 20.41/20.60  thf('111', plain,
% 20.41/20.60      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('demod', [status(thm)], ['109', '110'])).
% 20.41/20.60  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('113', plain, ((v2_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('114', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v2_struct_0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ sk_D)
% 20.41/20.60          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 20.41/20.60          | (v5_pre_topc @ 
% 20.41/20.60             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 20.41/20.60             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 20.41/20.60          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 20.41/20.60          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.41/20.60          | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60               sk_D @ sk_B)
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['56', '78', '79', '80', '81', '82', '83', '84', '85', '86', 
% 20.41/20.60                 '98', '99', '111', '112', '113'])).
% 20.41/20.60  thf('115', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 20.41/20.60        | (v1_funct_1 @ sk_C))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('116', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('split', [status(esa)], ['115'])).
% 20.41/20.60  thf('117', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('118', plain,
% 20.41/20.60      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('demod', [status(thm)], ['116', '117'])).
% 20.41/20.60  thf('119', plain,
% 20.41/20.60      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.41/20.60        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('120', plain,
% 20.41/20.60      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('split', [status(esa)], ['119'])).
% 20.41/20.60  thf('121', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 20.41/20.60  thf('122', plain,
% 20.41/20.60      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_E))),
% 20.41/20.60      inference('simplify', [status(thm)], ['39'])).
% 20.41/20.60  thf('123', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 20.41/20.60  thf('124', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('125', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (k1_zfmisc_1 @ 
% 20.41/20.60            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['60', '63', '66', '67', '68'])).
% 20.41/20.60  thf('126', plain,
% 20.41/20.60      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 20.41/20.60         ((v2_struct_0 @ X28)
% 20.41/20.60          | ~ (v2_pre_topc @ X28)
% 20.41/20.60          | ~ (l1_pre_topc @ X28)
% 20.41/20.60          | (v2_struct_0 @ X29)
% 20.41/20.60          | ~ (m1_pre_topc @ X29 @ X30)
% 20.41/20.60          | ~ (v1_funct_1 @ 
% 20.41/20.60               (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)))
% 20.41/20.60          | ~ (v1_funct_2 @ 
% 20.41/20.60               (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60               (u1_struct_0 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60               (u1_struct_0 @ X28))
% 20.41/20.60          | ~ (v5_pre_topc @ 
% 20.41/20.60               (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60               (k1_tsep_1 @ X30 @ X32 @ X29) @ X28)
% 20.41/20.60          | ~ (m1_subset_1 @ 
% 20.41/20.60               (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60                 (u1_struct_0 @ X28))))
% 20.41/20.60          | (v5_pre_topc @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X29) @ X29 @ X28)
% 20.41/20.60          | ~ (m1_subset_1 @ X31 @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))))
% 20.41/20.60          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))
% 20.41/20.60          | ~ (v1_funct_1 @ X31)
% 20.41/20.60          | ~ (r4_tsep_1 @ X30 @ X32 @ X29)
% 20.41/20.60          | ~ (m1_pre_topc @ X32 @ X30)
% 20.41/20.60          | (v2_struct_0 @ X32)
% 20.41/20.60          | ~ (l1_pre_topc @ X30)
% 20.41/20.60          | ~ (v2_pre_topc @ X30)
% 20.41/20.60          | (v2_struct_0 @ X30))),
% 20.41/20.60      inference('cnf', [status(esa)], [t129_tmap_1])).
% 20.41/20.60  thf('127', plain,
% 20.41/20.60      (![X0 : $i, X1 : $i]:
% 20.41/20.60         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 20.41/20.60          | (v2_struct_0 @ sk_A)
% 20.41/20.60          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X1)
% 20.41/20.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 20.41/20.60          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 20.41/20.60          | ~ (v1_funct_1 @ sk_C)
% 20.41/20.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (m1_subset_1 @ sk_C @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 20.41/20.60          | ~ (v5_pre_topc @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 20.41/20.60          | ~ (v1_funct_2 @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (v1_funct_1 @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_B)
% 20.41/20.60          | ~ (v2_pre_topc @ sk_B)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['125', '126'])).
% 20.41/20.60  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('131', plain,
% 20.41/20.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('132', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('133', plain, ((l1_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('134', plain, ((v2_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('135', plain,
% 20.41/20.60      (![X0 : $i, X1 : $i]:
% 20.41/20.60         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 20.41/20.60          | (v2_struct_0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X1)
% 20.41/20.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 20.41/20.60          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 20.41/20.60          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 20.41/20.60          | ~ (v5_pre_topc @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 20.41/20.60          | ~ (v1_funct_2 @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (v1_funct_1 @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['127', '128', '129', '130', '131', '132', '133', '134'])).
% 20.41/20.60  thf('136', plain,
% 20.41/20.60      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 20.41/20.60           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.41/20.60           (u1_struct_0 @ sk_B))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 20.41/20.60        | ~ (v1_funct_1 @ 
% 20.41/20.60             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 20.41/20.60        | ~ (v5_pre_topc @ 
% 20.41/20.60             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.41/20.60             (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 20.41/20.60        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 20.41/20.60        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 20.41/20.60        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['124', '135'])).
% 20.41/20.60  thf('137', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('138', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('139', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('140', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('141', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('142', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('143', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('144', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('145', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('147', plain,
% 20.41/20.60      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 20.41/20.60           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['136', '137', '138', '139', '140', '141', '142', '143', 
% 20.41/20.60                 '144', '145', '146'])).
% 20.41/20.60  thf('148', plain,
% 20.41/20.60      ((~ (l1_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['123', '147'])).
% 20.41/20.60  thf('149', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('150', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['148', '149'])).
% 20.41/20.60  thf('151', plain,
% 20.41/20.60      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('sup-', [status(thm)], ['122', '150'])).
% 20.41/20.60  thf('152', plain,
% 20.41/20.60      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('simplify', [status(thm)], ['151'])).
% 20.41/20.60  thf('153', plain,
% 20.41/20.60      ((~ (l1_struct_0 @ sk_A)
% 20.41/20.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60           sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['121', '152'])).
% 20.41/20.60  thf('154', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('155', plain,
% 20.41/20.60      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60           sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['153', '154'])).
% 20.41/20.60  thf('156', plain,
% 20.41/20.60      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60          sk_B)
% 20.41/20.60         | (v2_struct_0 @ sk_B)
% 20.41/20.60         | (v2_struct_0 @ sk_D)
% 20.41/20.60         | (v2_struct_0 @ sk_A)
% 20.41/20.60         | (v2_struct_0 @ sk_E))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['120', '155'])).
% 20.41/20.60  thf('157', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('158', plain,
% 20.41/20.60      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.41/20.60           (k1_zfmisc_1 @ 
% 20.41/20.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.41/20.60             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 20.41/20.60        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.41/20.60             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.41/20.60        | ~ (m1_subset_1 @ sk_C @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (v1_funct_1 @ sk_C))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('159', plain,
% 20.41/20.60      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 20.41/20.60         <= (~
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('split', [status(esa)], ['158'])).
% 20.41/20.60  thf('160', plain,
% 20.41/20.60      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60           sk_B))
% 20.41/20.60         <= (~
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['157', '159'])).
% 20.41/20.60  thf('161', plain,
% 20.41/20.60      ((((v2_struct_0 @ sk_E)
% 20.41/20.60         | (v2_struct_0 @ sk_A)
% 20.41/20.60         | (v2_struct_0 @ sk_D)
% 20.41/20.60         | (v2_struct_0 @ sk_B)))
% 20.41/20.60         <= (~
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['156', '160'])).
% 20.41/20.60  thf('162', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('163', plain,
% 20.41/20.60      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 20.41/20.60         <= (~
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['161', '162'])).
% 20.41/20.60  thf('164', plain, (~ (v2_struct_0 @ sk_D)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('165', plain,
% 20.41/20.60      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 20.41/20.60         <= (~
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('clc', [status(thm)], ['163', '164'])).
% 20.41/20.60  thf('166', plain, (~ (v2_struct_0 @ sk_E)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('167', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_A))
% 20.41/20.60         <= (~
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('clc', [status(thm)], ['165', '166'])).
% 20.41/20.60  thf('168', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('169', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 20.41/20.60       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['167', '168'])).
% 20.41/20.60  thf('170', plain,
% 20.41/20.60      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('split', [status(esa)], ['119'])).
% 20.41/20.60  thf('171', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 20.41/20.60  thf('172', plain,
% 20.41/20.60      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_E))),
% 20.41/20.60      inference('simplify', [status(thm)], ['39'])).
% 20.41/20.60  thf('173', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 20.41/20.60  thf('174', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('175', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (k1_zfmisc_1 @ 
% 20.41/20.60            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['60', '63', '66', '67', '68'])).
% 20.41/20.60  thf('176', plain,
% 20.41/20.60      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 20.41/20.60         ((v2_struct_0 @ X28)
% 20.41/20.60          | ~ (v2_pre_topc @ X28)
% 20.41/20.60          | ~ (l1_pre_topc @ X28)
% 20.41/20.60          | (v2_struct_0 @ X29)
% 20.41/20.60          | ~ (m1_pre_topc @ X29 @ X30)
% 20.41/20.60          | ~ (v1_funct_1 @ 
% 20.41/20.60               (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)))
% 20.41/20.60          | ~ (v1_funct_2 @ 
% 20.41/20.60               (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60               (u1_struct_0 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60               (u1_struct_0 @ X28))
% 20.41/20.60          | ~ (v5_pre_topc @ 
% 20.41/20.60               (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60               (k1_tsep_1 @ X30 @ X32 @ X29) @ X28)
% 20.41/20.60          | ~ (m1_subset_1 @ 
% 20.41/20.60               (k2_tmap_1 @ X30 @ X28 @ X31 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X30 @ X32 @ X29)) @ 
% 20.41/20.60                 (u1_struct_0 @ X28))))
% 20.41/20.60          | (v5_pre_topc @ (k2_tmap_1 @ X30 @ X28 @ X31 @ X32) @ X32 @ X28)
% 20.41/20.60          | ~ (m1_subset_1 @ X31 @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))))
% 20.41/20.60          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))
% 20.41/20.60          | ~ (v1_funct_1 @ X31)
% 20.41/20.60          | ~ (r4_tsep_1 @ X30 @ X32 @ X29)
% 20.41/20.60          | ~ (m1_pre_topc @ X32 @ X30)
% 20.41/20.60          | (v2_struct_0 @ X32)
% 20.41/20.60          | ~ (l1_pre_topc @ X30)
% 20.41/20.60          | ~ (v2_pre_topc @ X30)
% 20.41/20.60          | (v2_struct_0 @ X30))),
% 20.41/20.60      inference('cnf', [status(esa)], [t129_tmap_1])).
% 20.41/20.60  thf('177', plain,
% 20.41/20.60      (![X0 : $i, X1 : $i]:
% 20.41/20.60         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 20.41/20.60          | (v2_struct_0 @ sk_A)
% 20.41/20.60          | ~ (v2_pre_topc @ sk_A)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X1)
% 20.41/20.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 20.41/20.60          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 20.41/20.60          | ~ (v1_funct_1 @ sk_C)
% 20.41/20.60          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (m1_subset_1 @ sk_C @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X1 @ sk_B)
% 20.41/20.60          | ~ (v5_pre_topc @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 20.41/20.60          | ~ (v1_funct_2 @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (v1_funct_1 @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | ~ (l1_pre_topc @ sk_B)
% 20.41/20.60          | ~ (v2_pre_topc @ sk_B)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['175', '176'])).
% 20.41/20.60  thf('178', plain, ((v2_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('181', plain,
% 20.41/20.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('182', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('183', plain, ((l1_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('184', plain, ((v2_pre_topc @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('185', plain,
% 20.41/20.60      (![X0 : $i, X1 : $i]:
% 20.41/20.60         (~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0))
% 20.41/20.60          | (v2_struct_0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X1)
% 20.41/20.60          | ~ (m1_pre_topc @ X1 @ sk_A)
% 20.41/20.60          | ~ (r4_tsep_1 @ sk_A @ X1 @ X0)
% 20.41/20.60          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X1) @ X1 @ sk_B)
% 20.41/20.60          | ~ (v5_pre_topc @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (k1_tsep_1 @ sk_A @ X1 @ X0) @ sk_B)
% 20.41/20.60          | ~ (v1_funct_2 @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ X1 @ X0)) @ 
% 20.41/20.60               (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (v1_funct_1 @ 
% 20.41/20.60               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ X1 @ X0)))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['177', '178', '179', '180', '181', '182', '183', '184'])).
% 20.41/20.60  thf('186', plain,
% 20.41/20.60      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 20.41/20.60           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.41/20.60           (u1_struct_0 @ sk_B))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 20.41/20.60        | ~ (v1_funct_1 @ 
% 20.41/20.60             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 20.41/20.60        | ~ (v5_pre_topc @ 
% 20.41/20.60             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.41/20.60             (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 20.41/20.60        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 20.41/20.60        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 20.41/20.60        | ~ (m1_pre_topc @ sk_D @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['174', '185'])).
% 20.41/20.60  thf('187', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('188', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('189', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('190', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('191', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('192', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('193', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('194', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('195', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('196', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('197', plain,
% 20.41/20.60      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 20.41/20.60           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['186', '187', '188', '189', '190', '191', '192', '193', 
% 20.41/20.60                 '194', '195', '196'])).
% 20.41/20.60  thf('198', plain,
% 20.41/20.60      ((~ (l1_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['173', '197'])).
% 20.41/20.60  thf('199', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('200', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['198', '199'])).
% 20.41/20.60  thf('201', plain,
% 20.41/20.60      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('sup-', [status(thm)], ['172', '200'])).
% 20.41/20.60  thf('202', plain,
% 20.41/20.60      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('simplify', [status(thm)], ['201'])).
% 20.41/20.60  thf('203', plain,
% 20.41/20.60      ((~ (l1_struct_0 @ sk_A)
% 20.41/20.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.41/20.60           sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['171', '202'])).
% 20.41/20.60  thf('204', plain, ((l1_struct_0 @ sk_A)),
% 20.41/20.60      inference('sup-', [status(thm)], ['61', '62'])).
% 20.41/20.60  thf('205', plain,
% 20.41/20.60      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.41/20.60           sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['203', '204'])).
% 20.41/20.60  thf('206', plain,
% 20.41/20.60      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.41/20.60          sk_B)
% 20.41/20.60         | (v2_struct_0 @ sk_B)
% 20.41/20.60         | (v2_struct_0 @ sk_D)
% 20.41/20.60         | (v2_struct_0 @ sk_A)
% 20.41/20.60         | (v2_struct_0 @ sk_E))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['170', '205'])).
% 20.41/20.60  thf('207', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('208', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 20.41/20.60        | (v1_funct_1 @ sk_C))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('209', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('split', [status(esa)], ['208'])).
% 20.41/20.60  thf('210', plain,
% 20.41/20.60      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('sup+', [status(thm)], ['207', '209'])).
% 20.41/20.60  thf('211', plain,
% 20.41/20.60      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.41/20.60           (k1_zfmisc_1 @ 
% 20.41/20.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.41/20.60             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 20.41/20.60        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.41/20.60             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.41/20.60        | ~ (m1_subset_1 @ sk_C @ 
% 20.41/20.60             (k1_zfmisc_1 @ 
% 20.41/20.60              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (v1_funct_1 @ sk_C))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('212', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('213', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('214', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (k1_zfmisc_1 @ 
% 20.41/20.60            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['60', '63', '66', '67', '68'])).
% 20.41/20.60  thf('215', plain,
% 20.41/20.60      (((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.41/20.60         (k1_zfmisc_1 @ 
% 20.41/20.60          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | ~ (l1_struct_0 @ sk_E))),
% 20.41/20.60      inference('sup+', [status(thm)], ['213', '214'])).
% 20.41/20.60  thf('216', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('217', plain,
% 20.41/20.60      (![X15 : $i, X16 : $i]:
% 20.41/20.60         (~ (m1_pre_topc @ X15 @ X16)
% 20.41/20.60          | (l1_pre_topc @ X15)
% 20.41/20.60          | ~ (l1_pre_topc @ X16))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 20.41/20.60  thf('218', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_E))),
% 20.41/20.60      inference('sup-', [status(thm)], ['216', '217'])).
% 20.41/20.60  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('220', plain, ((l1_pre_topc @ sk_E)),
% 20.41/20.60      inference('demod', [status(thm)], ['218', '219'])).
% 20.41/20.60  thf('221', plain,
% 20.41/20.60      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 20.41/20.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 20.41/20.60  thf('222', plain, ((l1_struct_0 @ sk_E)),
% 20.41/20.60      inference('sup-', [status(thm)], ['220', '221'])).
% 20.41/20.60  thf('223', plain,
% 20.41/20.60      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('demod', [status(thm)], ['215', '222'])).
% 20.41/20.60  thf('224', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('225', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('226', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('227', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 20.41/20.60  thf('228', plain,
% 20.41/20.60      (((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.41/20.60         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (l1_struct_0 @ sk_E))),
% 20.41/20.60      inference('sup+', [status(thm)], ['226', '227'])).
% 20.41/20.60  thf('229', plain, ((l1_struct_0 @ sk_E)),
% 20.41/20.60      inference('sup-', [status(thm)], ['220', '221'])).
% 20.41/20.60  thf('230', plain,
% 20.41/20.60      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.41/20.60        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['228', '229'])).
% 20.41/20.60  thf('231', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('232', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('233', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.41/20.60          | ~ (l1_struct_0 @ X0))),
% 20.41/20.60      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 20.41/20.60  thf('234', plain,
% 20.41/20.60      (((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 20.41/20.60        | ~ (l1_struct_0 @ sk_E))),
% 20.41/20.60      inference('sup+', [status(thm)], ['232', '233'])).
% 20.41/20.60  thf('235', plain, ((l1_struct_0 @ sk_E)),
% 20.41/20.60      inference('sup-', [status(thm)], ['220', '221'])).
% 20.41/20.60  thf('236', plain,
% 20.41/20.60      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('demod', [status(thm)], ['234', '235'])).
% 20.41/20.60  thf('237', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('238', plain,
% 20.41/20.60      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('demod', [status(thm)], ['70', '77'])).
% 20.41/20.60  thf('239', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('240', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('241', plain,
% 20.41/20.60      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['96', '97'])).
% 20.41/20.60  thf('242', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('clc', [status(thm)], ['52', '53'])).
% 20.41/20.60  thf('243', plain,
% 20.41/20.60      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.41/20.60      inference('demod', [status(thm)], ['109', '110'])).
% 20.41/20.60  thf('244', plain,
% 20.41/20.60      ((m1_subset_1 @ sk_C @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('245', plain,
% 20.41/20.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('247', plain,
% 20.41/20.60      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.41/20.60           sk_B)
% 20.41/20.60        | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['211', '212', '223', '224', '225', '230', '231', '236', 
% 20.41/20.60                 '237', '238', '239', '240', '241', '242', '243', '244', 
% 20.41/20.60                 '245', '246'])).
% 20.41/20.60  thf('248', plain,
% 20.41/20.60      (((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60         | ~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ 
% 20.41/20.60              sk_D @ sk_B)))
% 20.41/20.60         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['210', '247'])).
% 20.41/20.60  thf('249', plain,
% 20.41/20.60      ((((v2_struct_0 @ sk_E)
% 20.41/20.60         | (v2_struct_0 @ sk_A)
% 20.41/20.60         | (v2_struct_0 @ sk_D)
% 20.41/20.60         | (v2_struct_0 @ sk_B)
% 20.41/20.60         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 20.41/20.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['206', '248'])).
% 20.41/20.60  thf('250', plain,
% 20.41/20.60      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('split', [status(esa)], ['119'])).
% 20.41/20.60  thf('251', plain,
% 20.41/20.60      ((((v2_struct_0 @ sk_E)
% 20.41/20.60         | (v2_struct_0 @ sk_A)
% 20.41/20.60         | (v2_struct_0 @ sk_D)
% 20.41/20.60         | (v2_struct_0 @ sk_B)))
% 20.41/20.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('demod', [status(thm)], ['249', '250'])).
% 20.41/20.60  thf('252', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('253', plain,
% 20.41/20.60      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 20.41/20.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('sup-', [status(thm)], ['251', '252'])).
% 20.41/20.60  thf('254', plain, (~ (v2_struct_0 @ sk_D)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('255', plain,
% 20.41/20.60      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 20.41/20.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('clc', [status(thm)], ['253', '254'])).
% 20.41/20.60  thf('256', plain, (~ (v2_struct_0 @ sk_E)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('257', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_A))
% 20.41/20.60         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.41/20.60             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('clc', [status(thm)], ['255', '256'])).
% 20.41/20.60  thf('258', plain, (~ (v2_struct_0 @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('259', plain,
% 20.41/20.60      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 20.41/20.60       ~
% 20.41/20.60       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['257', '258'])).
% 20.41/20.60  thf('260', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 20.41/20.60        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('261', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 20.41/20.60       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('split', [status(esa)], ['260'])).
% 20.41/20.60  thf('262', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 20.41/20.60      inference('sat_resolution*', [status(thm)], ['169', '259', '261'])).
% 20.41/20.60  thf('263', plain,
% 20.41/20.60      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)),
% 20.41/20.60      inference('simpl_trail', [status(thm)], ['118', '262'])).
% 20.41/20.60  thf('264', plain,
% 20.41/20.60      (![X0 : $i]:
% 20.41/20.60         ((v2_struct_0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ sk_D)
% 20.41/20.60          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 20.41/20.60          | (v5_pre_topc @ 
% 20.41/20.60             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 20.41/20.60             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 20.41/20.60          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60               (k1_zfmisc_1 @ 
% 20.41/20.60                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 20.41/20.60          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.41/20.60               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.41/20.60          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.41/20.60          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.41/20.60          | (v2_struct_0 @ X0)
% 20.41/20.60          | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['114', '263'])).
% 20.41/20.60  thf('265', plain,
% 20.41/20.60      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.41/20.60           (k1_zfmisc_1 @ 
% 20.41/20.60            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 20.41/20.60        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 20.41/20.60        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.41/20.60             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 20.41/20.60        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60             sk_B)
% 20.41/20.60        | (v5_pre_topc @ 
% 20.41/20.60           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.41/20.60           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 20.41/20.60        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('sup-', [status(thm)], ['47', '264'])).
% 20.41/20.60  thf('266', plain,
% 20.41/20.60      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.41/20.60        (k1_zfmisc_1 @ 
% 20.41/20.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 20.41/20.60      inference('demod', [status(thm)], ['215', '222'])).
% 20.41/20.60  thf('267', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('268', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('269', plain,
% 20.41/20.60      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('demod', [status(thm)], ['234', '235'])).
% 20.41/20.60  thf('270', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('271', plain,
% 20.41/20.60      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.41/20.60        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 20.41/20.60      inference('demod', [status(thm)], ['228', '229'])).
% 20.41/20.60  thf('272', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('273', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('split', [status(esa)], ['208'])).
% 20.41/20.60  thf('274', plain,
% 20.41/20.60      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.41/20.60         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.41/20.60      inference('clc', [status(thm)], ['45', '46'])).
% 20.41/20.60  thf('275', plain,
% 20.41/20.60      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 20.41/20.60         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.41/20.60               sk_B)))),
% 20.41/20.60      inference('demod', [status(thm)], ['273', '274'])).
% 20.41/20.60  thf('276', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 20.41/20.60        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('277', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 20.41/20.60       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('split', [status(esa)], ['276'])).
% 20.41/20.60  thf('278', plain,
% 20.41/20.60      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 20.41/20.60      inference('sat_resolution*', [status(thm)], ['169', '259', '277'])).
% 20.41/20.60  thf('279', plain,
% 20.41/20.60      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)),
% 20.41/20.60      inference('simpl_trail', [status(thm)], ['275', '278'])).
% 20.41/20.60  thf('280', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('281', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('282', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('283', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('demod', [status(thm)],
% 20.41/20.60                ['265', '266', '267', '268', '269', '270', '271', '272', 
% 20.41/20.60                 '279', '280', '281', '282'])).
% 20.41/20.60  thf('284', plain,
% 20.41/20.60      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('sup+', [status(thm)], ['40', '283'])).
% 20.41/20.60  thf('285', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_B)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_E)
% 20.41/20.60        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('simplify', [status(thm)], ['284'])).
% 20.41/20.60  thf('286', plain,
% 20.41/20.60      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 20.41/20.60         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.41/20.60      inference('split', [status(esa)], ['158'])).
% 20.41/20.60  thf('287', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.41/20.60      inference('sat_resolution*', [status(thm)], ['169', '259'])).
% 20.41/20.60  thf('288', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 20.41/20.60      inference('simpl_trail', [status(thm)], ['286', '287'])).
% 20.41/20.60  thf('289', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_E)
% 20.41/20.60        | (v2_struct_0 @ sk_A)
% 20.41/20.60        | (v2_struct_0 @ sk_D)
% 20.41/20.60        | (v2_struct_0 @ sk_B))),
% 20.41/20.60      inference('sup-', [status(thm)], ['285', '288'])).
% 20.41/20.60  thf('290', plain, (~ (v2_struct_0 @ sk_B)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('291', plain,
% 20.41/20.60      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E))),
% 20.41/20.60      inference('sup-', [status(thm)], ['289', '290'])).
% 20.41/20.60  thf('292', plain, (~ (v2_struct_0 @ sk_D)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('293', plain, (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A))),
% 20.41/20.60      inference('clc', [status(thm)], ['291', '292'])).
% 20.41/20.60  thf('294', plain, (~ (v2_struct_0 @ sk_E)),
% 20.41/20.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.41/20.60  thf('295', plain, ((v2_struct_0 @ sk_A)),
% 20.41/20.60      inference('clc', [status(thm)], ['293', '294'])).
% 20.41/20.60  thf('296', plain, ($false), inference('demod', [status(thm)], ['0', '295'])).
% 20.41/20.60  
% 20.41/20.60  % SZS output end Refutation
% 20.41/20.60  
% 20.41/20.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
