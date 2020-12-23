%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.APC4e0QQAx

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:07 EST 2020

% Result     : Theorem 20.02s
% Output     : Refutation 20.12s
% Verified   : 
% Statistics : Number of formulae       :  362 (4126 expanded)
%              Number of leaves         :   41 (1215 expanded)
%              Depth                    :   34
%              Number of atoms          : 4938 (274493 expanded)
%              Number of equality atoms :   56 (2146 expanded)
%              Maximal formula depth    :   30 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r4_tsep_1_type,type,(
    r4_tsep_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X32 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X32 @ X31 @ X33 ) @ X32 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X30 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k2_partfun1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','35'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('37',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k7_relat_1 @ X15 @ X16 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('40',plain,
    ( ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','40'])).

thf('42',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_struct_0 @ X36 )
      | ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X37 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X35 @ X36 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('56',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','57','60','61','62'])).

thf('64',plain,
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

thf('65',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['74'])).

thf('76',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['51','75'])).

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

thf('77',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X40 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X42 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X42 ) @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X42 ) @ X42 @ X38 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X39 ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X39 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X39 ) @ X39 @ X38 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( r4_tsep_1 @ X40 @ X42 @ X39 )
      | ~ ( m1_pre_topc @ X42 @ X40 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
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
    inference('sup-',[status(thm)],['76','77'])).

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
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_struct_0 @ X36 )
      | ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X37 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X35 @ X36 @ X34 @ X37 ) @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('92',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('95',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('96',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('98',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['98'])).

thf('100',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['86','99'])).

thf('101',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X36 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_struct_0 @ X36 )
      | ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X37 )
      | ( v1_funct_1 @ ( k2_tmap_1 @ X35 @ X36 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('107',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['64'])).

thf('112',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['71','72'])).

thf('114',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['114'])).

thf('116',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['102','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r4_tsep_1 @ sk_A @ sk_D @ X0 )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83','84','100','116','117','118'])).

thf('120',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16','21','22','23'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['127'])).

thf('129',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('130',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('134',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['41'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','57','60','61','62'])).

thf('137',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X40 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X39 ) @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( r4_tsep_1 @ X40 @ X42 @ X39 )
      | ~ ( m1_pre_topc @ X42 @ X40 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('139',plain,(
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
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E ) @ sk_E @ X0 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E ) @ sk_E @ X0 )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ sk_A @ X0 )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143','144','145','146','147','148','149','150'])).

thf('152',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','151'])).

thf('153',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('154',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('157',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153','154','155','156','157','158','159'])).

thf('161',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['135','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
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
    inference('sup-',[status(thm)],['134','163'])).

thf('165',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['133','165'])).

thf('167',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('168',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['132','168'])).

thf('170',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('171',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['64'])).

thf('172',plain,
    ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('174',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['131'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('184',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference(simplify,[status(thm)],['41'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','57','60','61','62'])).

thf('187',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X39 )
      | ~ ( m1_pre_topc @ X39 @ X40 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( u1_struct_0 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) @ X38 )
      | ~ ( m1_subset_1 @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X40 @ X42 @ X39 ) ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ( v5_pre_topc @ ( k2_tmap_1 @ X40 @ X38 @ X41 @ X42 ) @ X42 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( r4_tsep_1 @ X40 @ X42 @ X39 )
      | ~ ( m1_pre_topc @ X42 @ X40 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t129_tmap_1])).

thf('189',plain,(
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
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
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
    inference(demod,[status(thm)],['189','190','191','192','193','194','195','196','197','198','199','200'])).

thf('202',plain,
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
    inference('sup-',[status(thm)],['186','201'])).

thf('203',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('204',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('207',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['202','203','204','205','206','207','208','209'])).

thf('211',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['185','210'])).

thf('212',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('213',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,
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
    inference('sup-',[status(thm)],['184','213'])).

thf('215',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['183','215'])).

thf('217',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('218',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,
    ( ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['182','218'])).

thf('220',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('221',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['221'])).

thf('223',plain,
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

thf('224',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','57','60','61','62'])).

thf('227',plain,
    ( ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['64'])).

thf('228',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('231',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_E ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    l1_pre_topc @ sk_E ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('235',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['228','235'])).

thf('237',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['236'])).

thf('238',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['225','237'])).

thf('239',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92','93'])).

thf('242',plain,
    ( ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['64'])).

thf('243',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['233','234'])).

thf('245',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['245'])).

thf('247',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['240','246'])).

thf('248',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( v1_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('251',plain,
    ( ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(split,[status(esa)],['64'])).

thf('252',plain,
    ( ~ ( l1_struct_0 @ sk_E )
   <= ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    l1_struct_0 @ sk_E ),
    inference('sup-',[status(thm)],['233','234'])).

thf('254',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['254'])).

thf('256',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['249','255'])).

thf('257',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['51','75'])).

thf('258',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['86','99'])).

thf('259',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['102','115'])).

thf('260',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['223','238','247','256','257','258','259','260','261','262'])).

thf('264',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ) )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['222','263'])).

thf('265',plain,
    ( ( ~ ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['220','264'])).

thf('266',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','265'])).

thf('267',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['131'])).

thf('268',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      & ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ) ),
    inference(clc,[status(thm)],['272','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ~ ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['277'])).

thf('279',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_D @ sk_B ),
    inference('sat_resolution*',[status(thm)],['181','276','278'])).

thf('280',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_D ) ) @ sk_D @ sk_B ),
    inference(simpl_trail,[status(thm)],['130','279'])).

thf('281',plain,(
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
    inference(demod,[status(thm)],['119','126','280'])).

thf('282',plain,
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
    inference('sup-',[status(thm)],['49','281'])).

thf('283',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['225','237'])).

thf('284',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('285',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['283','284'])).

thf('286',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('288',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['249','255'])).

thf('289',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('290',plain,(
    v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('292',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['240','246'])).

thf('293',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('294',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ ( u1_struct_0 @ sk_E ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['292','293'])).

thf('295',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('296',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(split,[status(esa)],['221'])).

thf('297',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('298',plain,
    ( ( v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B )
   <= ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['296','297'])).

thf('299',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['299'])).

thf('301',plain,(
    v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_E @ sk_B ),
    inference('sat_resolution*',[status(thm)],['181','276','300'])).

thf('302',plain,(
    v5_pre_topc @ ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_E ) ) @ sk_E @ sk_B ),
    inference(simpl_trail,[status(thm)],['298','301'])).

thf('303',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    r4_tsep_1 @ sk_A @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['282','285','286','287','290','291','294','295','302','303','304','305'])).

thf('307',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','306'])).

thf('308',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['64'])).

thf('310',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['181','276'])).

thf('311',plain,(
    ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['309','310'])).

thf('312',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['308','311'])).

thf('313',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['312','313'])).

thf('315',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['314','315'])).

thf('317',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['316','317'])).

thf('319',plain,(
    $false ),
    inference(demod,[status(thm)],['0','318'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.APC4e0QQAx
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 20.02/20.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.02/20.30  % Solved by: fo/fo7.sh
% 20.02/20.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.02/20.30  % done 5341 iterations in 19.831s
% 20.02/20.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.02/20.30  % SZS output start Refutation
% 20.02/20.30  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 20.02/20.30  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.02/20.30  thf(r4_tsep_1_type, type, r4_tsep_1: $i > $i > $i > $o).
% 20.02/20.30  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 20.02/20.30  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 20.02/20.30  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 20.02/20.30  thf(sk_B_type, type, sk_B: $i).
% 20.02/20.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.02/20.30  thf(sk_A_type, type, sk_A: $i).
% 20.02/20.30  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 20.02/20.30  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 20.02/20.30  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 20.02/20.30  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 20.02/20.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 20.02/20.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.02/20.30  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 20.02/20.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.02/20.30  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.02/20.30  thf(sk_E_type, type, sk_E: $i).
% 20.02/20.30  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 20.02/20.30  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 20.02/20.30  thf(sk_D_type, type, sk_D: $i).
% 20.02/20.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.02/20.30  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 20.02/20.30  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 20.02/20.30  thf(sk_C_type, type, sk_C: $i).
% 20.02/20.30  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 20.02/20.30  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 20.02/20.30  thf(t132_tmap_1, conjecture,
% 20.02/20.30    (![A:$i]:
% 20.02/20.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.02/20.30       ( ![B:$i]:
% 20.02/20.30         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 20.02/20.30             ( l1_pre_topc @ B ) ) =>
% 20.02/20.30           ( ![C:$i]:
% 20.02/20.30             ( ( ( v1_funct_1 @ C ) & 
% 20.02/20.30                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                 ( m1_subset_1 @
% 20.02/20.30                   C @ 
% 20.02/20.30                   ( k1_zfmisc_1 @
% 20.02/20.30                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 20.02/20.30               ( ![D:$i]:
% 20.02/20.30                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 20.02/20.30                   ( ![E:$i]:
% 20.02/20.30                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 20.02/20.30                       ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 20.02/20.30                           ( r4_tsep_1 @ A @ D @ E ) ) =>
% 20.02/20.30                         ( ( ( v1_funct_1 @ C ) & 
% 20.02/20.30                             ( v1_funct_2 @
% 20.02/20.30                               C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                             ( v5_pre_topc @ C @ A @ B ) & 
% 20.02/20.30                             ( m1_subset_1 @
% 20.02/20.30                               C @ 
% 20.02/20.30                               ( k1_zfmisc_1 @
% 20.02/20.30                                 ( k2_zfmisc_1 @
% 20.02/20.30                                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 20.02/20.30                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 20.02/20.30                             ( v1_funct_2 @
% 20.02/20.30                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.02/20.30                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                             ( v5_pre_topc @
% 20.02/20.30                               ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 20.02/20.30                             ( m1_subset_1 @
% 20.02/20.30                               ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.02/20.30                               ( k1_zfmisc_1 @
% 20.02/20.30                                 ( k2_zfmisc_1 @
% 20.02/20.30                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 20.02/20.30                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 20.02/20.30                             ( v1_funct_2 @
% 20.02/20.30                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 20.02/20.30                               ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                             ( v5_pre_topc @
% 20.02/20.30                               ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 20.02/20.30                             ( m1_subset_1 @
% 20.02/20.30                               ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 20.02/20.30                               ( k1_zfmisc_1 @
% 20.02/20.30                                 ( k2_zfmisc_1 @
% 20.02/20.30                                   ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 20.02/20.30  thf(zf_stmt_0, negated_conjecture,
% 20.02/20.30    (~( ![A:$i]:
% 20.02/20.30        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 20.02/20.30            ( l1_pre_topc @ A ) ) =>
% 20.02/20.30          ( ![B:$i]:
% 20.02/20.30            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 20.02/20.30                ( l1_pre_topc @ B ) ) =>
% 20.02/20.30              ( ![C:$i]:
% 20.02/20.30                ( ( ( v1_funct_1 @ C ) & 
% 20.02/20.30                    ( v1_funct_2 @
% 20.02/20.30                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                    ( m1_subset_1 @
% 20.02/20.30                      C @ 
% 20.02/20.30                      ( k1_zfmisc_1 @
% 20.02/20.30                        ( k2_zfmisc_1 @
% 20.02/20.30                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 20.02/20.30                  ( ![D:$i]:
% 20.02/20.30                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 20.02/20.30                      ( ![E:$i]:
% 20.02/20.30                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 20.02/20.30                          ( ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) & 
% 20.02/20.30                              ( r4_tsep_1 @ A @ D @ E ) ) =>
% 20.02/20.30                            ( ( ( v1_funct_1 @ C ) & 
% 20.02/20.30                                ( v1_funct_2 @
% 20.02/20.30                                  C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                                ( v5_pre_topc @ C @ A @ B ) & 
% 20.02/20.30                                ( m1_subset_1 @
% 20.02/20.30                                  C @ 
% 20.02/20.30                                  ( k1_zfmisc_1 @
% 20.02/20.30                                    ( k2_zfmisc_1 @
% 20.02/20.30                                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) <=>
% 20.02/20.30                              ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 20.02/20.30                                ( v1_funct_2 @
% 20.02/20.30                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.02/20.30                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                                ( v5_pre_topc @
% 20.02/20.30                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ D @ B ) & 
% 20.02/20.30                                ( m1_subset_1 @
% 20.02/20.30                                  ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.02/20.30                                  ( k1_zfmisc_1 @
% 20.02/20.30                                    ( k2_zfmisc_1 @
% 20.02/20.30                                      ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 20.02/20.30                                ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ E ) ) & 
% 20.02/20.30                                ( v1_funct_2 @
% 20.02/20.30                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 20.02/20.30                                  ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                                ( v5_pre_topc @
% 20.02/20.30                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ E @ B ) & 
% 20.02/20.30                                ( m1_subset_1 @
% 20.02/20.30                                  ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 20.02/20.30                                  ( k1_zfmisc_1 @
% 20.02/20.30                                    ( k2_zfmisc_1 @
% 20.02/20.30                                      ( u1_struct_0 @ E ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 20.02/20.30    inference('cnf.neg', [status(esa)], [t132_tmap_1])).
% 20.02/20.30  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('1', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('2', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf(dt_k1_tsep_1, axiom,
% 20.02/20.30    (![A:$i,B:$i,C:$i]:
% 20.02/20.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 20.02/20.30         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 20.02/20.30         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 20.02/20.30       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 20.02/20.30         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 20.02/20.30         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 20.02/20.30  thf('3', plain,
% 20.02/20.30      (![X31 : $i, X32 : $i, X33 : $i]:
% 20.02/20.30         (~ (m1_pre_topc @ X31 @ X32)
% 20.02/20.30          | (v2_struct_0 @ X31)
% 20.02/20.30          | ~ (l1_pre_topc @ X32)
% 20.02/20.30          | (v2_struct_0 @ X32)
% 20.02/20.30          | (v2_struct_0 @ X33)
% 20.02/20.30          | ~ (m1_pre_topc @ X33 @ X32)
% 20.02/20.30          | (m1_pre_topc @ (k1_tsep_1 @ X32 @ X31 @ X33) @ X32))),
% 20.02/20.30      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 20.02/20.30  thf('4', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 20.02/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.02/20.30          | (v2_struct_0 @ X0)
% 20.02/20.30          | (v2_struct_0 @ sk_A)
% 20.02/20.30          | ~ (l1_pre_topc @ sk_A)
% 20.02/20.30          | (v2_struct_0 @ sk_D))),
% 20.02/20.30      inference('sup-', [status(thm)], ['2', '3'])).
% 20.02/20.30  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('6', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 20.02/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.02/20.30          | (v2_struct_0 @ X0)
% 20.02/20.30          | (v2_struct_0 @ sk_A)
% 20.02/20.30          | (v2_struct_0 @ sk_D))),
% 20.02/20.30      inference('demod', [status(thm)], ['4', '5'])).
% 20.02/20.30  thf('7', plain,
% 20.02/20.30      (((v2_struct_0 @ sk_D)
% 20.02/20.30        | (v2_struct_0 @ sk_A)
% 20.02/20.30        | (v2_struct_0 @ sk_E)
% 20.02/20.30        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_A))),
% 20.02/20.30      inference('sup-', [status(thm)], ['1', '6'])).
% 20.02/20.30  thf('8', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('9', plain,
% 20.02/20.30      (((v2_struct_0 @ sk_D)
% 20.02/20.30        | (v2_struct_0 @ sk_A)
% 20.02/20.30        | (v2_struct_0 @ sk_E)
% 20.02/20.30        | (m1_pre_topc @ sk_A @ sk_A))),
% 20.02/20.30      inference('demod', [status(thm)], ['7', '8'])).
% 20.02/20.30  thf('10', plain,
% 20.02/20.30      ((m1_subset_1 @ sk_C @ 
% 20.02/20.30        (k1_zfmisc_1 @ 
% 20.02/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf(d4_tmap_1, axiom,
% 20.02/20.30    (![A:$i]:
% 20.02/20.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.02/20.30       ( ![B:$i]:
% 20.02/20.30         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 20.02/20.30             ( l1_pre_topc @ B ) ) =>
% 20.02/20.30           ( ![C:$i]:
% 20.02/20.30             ( ( ( v1_funct_1 @ C ) & 
% 20.02/20.30                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30                 ( m1_subset_1 @
% 20.02/20.30                   C @ 
% 20.02/20.30                   ( k1_zfmisc_1 @
% 20.02/20.30                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 20.02/20.30               ( ![D:$i]:
% 20.02/20.30                 ( ( m1_pre_topc @ D @ A ) =>
% 20.02/20.30                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 20.02/20.30                     ( k2_partfun1 @
% 20.02/20.30                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 20.02/20.30                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 20.02/20.30  thf('11', plain,
% 20.02/20.30      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 20.02/20.30         ((v2_struct_0 @ X27)
% 20.02/20.30          | ~ (v2_pre_topc @ X27)
% 20.02/20.30          | ~ (l1_pre_topc @ X27)
% 20.02/20.30          | ~ (m1_pre_topc @ X28 @ X29)
% 20.02/20.30          | ((k2_tmap_1 @ X29 @ X27 @ X30 @ X28)
% 20.02/20.30              = (k2_partfun1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ 
% 20.02/20.30                 X30 @ (u1_struct_0 @ X28)))
% 20.02/20.30          | ~ (m1_subset_1 @ X30 @ 
% 20.02/20.30               (k1_zfmisc_1 @ 
% 20.02/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 20.02/20.30          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 20.02/20.30          | ~ (v1_funct_1 @ X30)
% 20.02/20.30          | ~ (l1_pre_topc @ X29)
% 20.02/20.30          | ~ (v2_pre_topc @ X29)
% 20.02/20.30          | (v2_struct_0 @ X29))),
% 20.02/20.30      inference('cnf', [status(esa)], [d4_tmap_1])).
% 20.02/20.30  thf('12', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         ((v2_struct_0 @ sk_A)
% 20.02/20.30          | ~ (v2_pre_topc @ sk_A)
% 20.02/20.30          | ~ (l1_pre_topc @ sk_A)
% 20.02/20.30          | ~ (v1_funct_1 @ sk_C)
% 20.02/20.30          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.02/20.30          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 20.02/20.30              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 20.02/20.30                 sk_C @ (u1_struct_0 @ X0)))
% 20.02/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.02/20.30          | ~ (l1_pre_topc @ sk_B)
% 20.02/20.30          | ~ (v2_pre_topc @ sk_B)
% 20.02/20.30          | (v2_struct_0 @ sk_B))),
% 20.02/20.30      inference('sup-', [status(thm)], ['10', '11'])).
% 20.02/20.30  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('16', plain,
% 20.02/20.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('17', plain,
% 20.02/20.30      ((m1_subset_1 @ sk_C @ 
% 20.02/20.30        (k1_zfmisc_1 @ 
% 20.02/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf(redefinition_k2_partfun1, axiom,
% 20.02/20.30    (![A:$i,B:$i,C:$i,D:$i]:
% 20.02/20.30     ( ( ( v1_funct_1 @ C ) & 
% 20.02/20.30         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.02/20.30       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 20.02/20.30  thf('18', plain,
% 20.02/20.30      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 20.02/20.30         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 20.02/20.30          | ~ (v1_funct_1 @ X20)
% 20.02/20.30          | ((k2_partfun1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 20.02/20.30      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 20.02/20.30  thf('19', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         (((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 20.02/20.30            X0) = (k7_relat_1 @ sk_C @ X0))
% 20.02/20.30          | ~ (v1_funct_1 @ sk_C))),
% 20.02/20.30      inference('sup-', [status(thm)], ['17', '18'])).
% 20.02/20.30  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('21', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         ((k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 20.02/20.30           X0) = (k7_relat_1 @ sk_C @ X0))),
% 20.02/20.30      inference('demod', [status(thm)], ['19', '20'])).
% 20.02/20.30  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('24', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         ((v2_struct_0 @ sk_A)
% 20.02/20.30          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 20.02/20.30              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 20.02/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.02/20.30          | (v2_struct_0 @ sk_B))),
% 20.02/20.30      inference('demod', [status(thm)],
% 20.02/20.30                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 20.02/20.30  thf('25', plain,
% 20.02/20.30      (((v2_struct_0 @ sk_E)
% 20.02/20.30        | (v2_struct_0 @ sk_A)
% 20.02/20.30        | (v2_struct_0 @ sk_D)
% 20.02/20.30        | (v2_struct_0 @ sk_B)
% 20.02/20.30        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A)
% 20.02/20.30            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))
% 20.02/20.30        | (v2_struct_0 @ sk_A))),
% 20.02/20.30      inference('sup-', [status(thm)], ['9', '24'])).
% 20.02/20.30  thf('26', plain,
% 20.02/20.30      ((m1_subset_1 @ sk_C @ 
% 20.02/20.30        (k1_zfmisc_1 @ 
% 20.02/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf(cc2_relset_1, axiom,
% 20.02/20.30    (![A:$i,B:$i,C:$i]:
% 20.02/20.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.02/20.30       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 20.02/20.30  thf('27', plain,
% 20.02/20.30      (![X17 : $i, X18 : $i, X19 : $i]:
% 20.02/20.30         ((v4_relat_1 @ X17 @ X18)
% 20.02/20.30          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 20.02/20.30      inference('cnf', [status(esa)], [cc2_relset_1])).
% 20.02/20.30  thf('28', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 20.02/20.30      inference('sup-', [status(thm)], ['26', '27'])).
% 20.02/20.30  thf(d18_relat_1, axiom,
% 20.02/20.30    (![A:$i,B:$i]:
% 20.02/20.30     ( ( v1_relat_1 @ B ) =>
% 20.02/20.30       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 20.02/20.30  thf('29', plain,
% 20.02/20.30      (![X11 : $i, X12 : $i]:
% 20.02/20.30         (~ (v4_relat_1 @ X11 @ X12)
% 20.02/20.30          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 20.02/20.30          | ~ (v1_relat_1 @ X11))),
% 20.02/20.30      inference('cnf', [status(esa)], [d18_relat_1])).
% 20.02/20.30  thf('30', plain,
% 20.02/20.30      ((~ (v1_relat_1 @ sk_C)
% 20.02/20.30        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 20.02/20.30      inference('sup-', [status(thm)], ['28', '29'])).
% 20.02/20.30  thf('31', plain,
% 20.02/20.30      ((m1_subset_1 @ sk_C @ 
% 20.02/20.30        (k1_zfmisc_1 @ 
% 20.02/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf(cc2_relat_1, axiom,
% 20.02/20.30    (![A:$i]:
% 20.02/20.30     ( ( v1_relat_1 @ A ) =>
% 20.02/20.30       ( ![B:$i]:
% 20.02/20.30         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 20.02/20.30  thf('32', plain,
% 20.02/20.30      (![X9 : $i, X10 : $i]:
% 20.02/20.30         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 20.02/20.30          | (v1_relat_1 @ X9)
% 20.02/20.30          | ~ (v1_relat_1 @ X10))),
% 20.02/20.30      inference('cnf', [status(esa)], [cc2_relat_1])).
% 20.02/20.30  thf('33', plain,
% 20.02/20.30      ((~ (v1_relat_1 @ 
% 20.02/20.30           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 20.02/20.30        | (v1_relat_1 @ sk_C))),
% 20.02/20.30      inference('sup-', [status(thm)], ['31', '32'])).
% 20.02/20.30  thf(fc6_relat_1, axiom,
% 20.02/20.30    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 20.02/20.30  thf('34', plain,
% 20.02/20.30      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 20.02/20.30      inference('cnf', [status(esa)], [fc6_relat_1])).
% 20.02/20.30  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 20.02/20.30      inference('demod', [status(thm)], ['33', '34'])).
% 20.02/20.30  thf('36', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 20.02/20.30      inference('demod', [status(thm)], ['30', '35'])).
% 20.02/20.30  thf(t97_relat_1, axiom,
% 20.02/20.30    (![A:$i,B:$i]:
% 20.02/20.30     ( ( v1_relat_1 @ B ) =>
% 20.02/20.30       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 20.02/20.30         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 20.02/20.30  thf('37', plain,
% 20.02/20.30      (![X15 : $i, X16 : $i]:
% 20.02/20.30         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 20.02/20.30          | ((k7_relat_1 @ X15 @ X16) = (X15))
% 20.02/20.30          | ~ (v1_relat_1 @ X15))),
% 20.02/20.30      inference('cnf', [status(esa)], [t97_relat_1])).
% 20.02/20.30  thf('38', plain,
% 20.02/20.30      ((~ (v1_relat_1 @ sk_C)
% 20.02/20.30        | ((k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C)))),
% 20.02/20.30      inference('sup-', [status(thm)], ['36', '37'])).
% 20.02/20.30  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 20.02/20.30      inference('demod', [status(thm)], ['33', '34'])).
% 20.02/20.30  thf('40', plain, (((k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 20.02/20.30      inference('demod', [status(thm)], ['38', '39'])).
% 20.02/20.30  thf('41', plain,
% 20.02/20.30      (((v2_struct_0 @ sk_E)
% 20.02/20.30        | (v2_struct_0 @ sk_A)
% 20.02/20.30        | (v2_struct_0 @ sk_D)
% 20.02/20.30        | (v2_struct_0 @ sk_B)
% 20.02/20.30        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 20.02/20.30        | (v2_struct_0 @ sk_A))),
% 20.02/20.30      inference('demod', [status(thm)], ['25', '40'])).
% 20.02/20.30  thf('42', plain,
% 20.02/20.30      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 20.02/20.30        | (v2_struct_0 @ sk_B)
% 20.02/20.30        | (v2_struct_0 @ sk_D)
% 20.02/20.30        | (v2_struct_0 @ sk_A)
% 20.02/20.30        | (v2_struct_0 @ sk_E))),
% 20.02/20.30      inference('simplify', [status(thm)], ['41'])).
% 20.02/20.30  thf('43', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('44', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         ((v2_struct_0 @ sk_A)
% 20.02/20.30          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 20.02/20.30              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 20.02/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.02/20.30          | (v2_struct_0 @ sk_B))),
% 20.02/20.30      inference('demod', [status(thm)],
% 20.02/20.30                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 20.02/20.30  thf('45', plain,
% 20.02/20.30      (((v2_struct_0 @ sk_B)
% 20.02/20.30        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.02/20.30            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))
% 20.02/20.30        | (v2_struct_0 @ sk_A))),
% 20.02/20.30      inference('sup-', [status(thm)], ['43', '44'])).
% 20.02/20.30  thf('46', plain, (~ (v2_struct_0 @ sk_B)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('47', plain,
% 20.02/20.30      (((v2_struct_0 @ sk_A)
% 20.02/20.30        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.02/20.30            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E))))),
% 20.02/20.30      inference('clc', [status(thm)], ['45', '46'])).
% 20.02/20.30  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('49', plain,
% 20.02/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.02/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.02/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.02/20.30  thf('50', plain,
% 20.02/20.30      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.02/20.30         (k1_zfmisc_1 @ 
% 20.02/20.30          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 20.02/20.30        | (v1_funct_1 @ sk_C))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('51', plain,
% 20.02/20.30      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.02/20.30         (k1_zfmisc_1 @ 
% 20.02/20.30          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 20.02/20.30         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.02/20.30               (k1_zfmisc_1 @ 
% 20.02/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 20.02/20.30      inference('split', [status(esa)], ['50'])).
% 20.02/20.30  thf('52', plain,
% 20.02/20.30      ((m1_subset_1 @ sk_C @ 
% 20.02/20.30        (k1_zfmisc_1 @ 
% 20.02/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf(dt_k2_tmap_1, axiom,
% 20.02/20.30    (![A:$i,B:$i,C:$i,D:$i]:
% 20.02/20.30     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 20.02/20.30         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.02/20.30         ( m1_subset_1 @
% 20.02/20.30           C @ 
% 20.02/20.30           ( k1_zfmisc_1 @
% 20.02/20.30             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 20.02/20.30         ( l1_struct_0 @ D ) ) =>
% 20.02/20.30       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 20.02/20.30         ( v1_funct_2 @
% 20.02/20.30           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 20.02/20.30           ( u1_struct_0 @ B ) ) & 
% 20.02/20.30         ( m1_subset_1 @
% 20.02/20.30           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 20.02/20.30           ( k1_zfmisc_1 @
% 20.02/20.30             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 20.02/20.30  thf('53', plain,
% 20.02/20.30      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 20.02/20.30         (~ (m1_subset_1 @ X34 @ 
% 20.02/20.30             (k1_zfmisc_1 @ 
% 20.02/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36))))
% 20.02/20.30          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36))
% 20.02/20.30          | ~ (v1_funct_1 @ X34)
% 20.02/20.30          | ~ (l1_struct_0 @ X36)
% 20.02/20.30          | ~ (l1_struct_0 @ X35)
% 20.02/20.30          | ~ (l1_struct_0 @ X37)
% 20.02/20.30          | (m1_subset_1 @ (k2_tmap_1 @ X35 @ X36 @ X34 @ X37) @ 
% 20.02/20.30             (k1_zfmisc_1 @ 
% 20.02/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X36)))))),
% 20.02/20.30      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 20.02/20.30  thf('54', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.02/20.30           (k1_zfmisc_1 @ 
% 20.02/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.02/20.30          | ~ (l1_struct_0 @ X0)
% 20.02/20.30          | ~ (l1_struct_0 @ sk_A)
% 20.02/20.30          | ~ (l1_struct_0 @ sk_B)
% 20.02/20.30          | ~ (v1_funct_1 @ sk_C)
% 20.02/20.30          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 20.02/20.30      inference('sup-', [status(thm)], ['52', '53'])).
% 20.02/20.30  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf(dt_l1_pre_topc, axiom,
% 20.02/20.30    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 20.02/20.30  thf('56', plain,
% 20.02/20.30      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 20.02/20.30      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 20.02/20.30  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 20.02/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.02/20.30  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('59', plain,
% 20.02/20.30      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 20.02/20.30      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 20.02/20.30  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 20.02/20.30      inference('sup-', [status(thm)], ['58', '59'])).
% 20.02/20.30  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('62', plain,
% 20.02/20.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('63', plain,
% 20.02/20.30      (![X0 : $i]:
% 20.02/20.30         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.02/20.30           (k1_zfmisc_1 @ 
% 20.02/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.02/20.30          | ~ (l1_struct_0 @ X0))),
% 20.02/20.30      inference('demod', [status(thm)], ['54', '57', '60', '61', '62'])).
% 20.02/20.30  thf('64', plain,
% 20.02/20.30      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.02/20.30           (k1_zfmisc_1 @ 
% 20.02/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 20.02/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.02/20.30             sk_B)
% 20.02/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.02/20.30             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 20.02/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 20.02/20.30        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.02/20.30             (k1_zfmisc_1 @ 
% 20.02/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 20.02/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.02/20.30             sk_B)
% 20.02/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.02/20.30             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 20.02/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.02/20.30        | ~ (m1_subset_1 @ sk_C @ 
% 20.02/20.30             (k1_zfmisc_1 @ 
% 20.02/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.02/20.30        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.02/20.30        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.02/20.30        | ~ (v1_funct_1 @ sk_C))),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf('65', plain,
% 20.02/20.30      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.02/20.30           (k1_zfmisc_1 @ 
% 20.02/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))
% 20.02/20.30         <= (~
% 20.02/20.30             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.02/20.30               (k1_zfmisc_1 @ 
% 20.02/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 20.02/20.30      inference('split', [status(esa)], ['64'])).
% 20.02/20.30  thf('66', plain,
% 20.02/20.30      ((~ (l1_struct_0 @ sk_D))
% 20.02/20.30         <= (~
% 20.02/20.30             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.02/20.30               (k1_zfmisc_1 @ 
% 20.02/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))))),
% 20.02/20.30      inference('sup-', [status(thm)], ['63', '65'])).
% 20.02/20.30  thf('67', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.02/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.02/20.30  thf(dt_m1_pre_topc, axiom,
% 20.02/20.30    (![A:$i]:
% 20.02/20.30     ( ( l1_pre_topc @ A ) =>
% 20.02/20.30       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 20.12/20.30  thf('68', plain,
% 20.12/20.30      (![X25 : $i, X26 : $i]:
% 20.12/20.30         (~ (m1_pre_topc @ X25 @ X26)
% 20.12/20.30          | (l1_pre_topc @ X25)
% 20.12/20.30          | ~ (l1_pre_topc @ X26))),
% 20.12/20.30      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 20.12/20.30  thf('69', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 20.12/20.30      inference('sup-', [status(thm)], ['67', '68'])).
% 20.12/20.30  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('71', plain, ((l1_pre_topc @ sk_D)),
% 20.12/20.30      inference('demod', [status(thm)], ['69', '70'])).
% 20.12/20.30  thf('72', plain,
% 20.12/20.30      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 20.12/20.30      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 20.12/20.30  thf('73', plain, ((l1_struct_0 @ sk_D)),
% 20.12/20.30      inference('sup-', [status(thm)], ['71', '72'])).
% 20.12/20.30  thf('74', plain,
% 20.12/20.30      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30         (k1_zfmisc_1 @ 
% 20.12/20.30          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 20.12/20.30      inference('demod', [status(thm)], ['66', '73'])).
% 20.12/20.30  thf('75', plain,
% 20.12/20.30      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30         (k1_zfmisc_1 @ 
% 20.12/20.30          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['74'])).
% 20.12/20.30  thf('76', plain,
% 20.12/20.30      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['51', '75'])).
% 20.12/20.30  thf(t129_tmap_1, axiom,
% 20.12/20.30    (![A:$i]:
% 20.12/20.30     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.12/20.30       ( ![B:$i]:
% 20.12/20.30         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 20.12/20.30             ( l1_pre_topc @ B ) ) =>
% 20.12/20.30           ( ![C:$i]:
% 20.12/20.30             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 20.12/20.30               ( ![D:$i]:
% 20.12/20.30                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 20.12/20.30                   ( ( r4_tsep_1 @ A @ C @ D ) =>
% 20.12/20.30                     ( ![E:$i]:
% 20.12/20.30                       ( ( ( v1_funct_1 @ E ) & 
% 20.12/20.30                           ( v1_funct_2 @
% 20.12/20.30                             E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 20.12/20.30                           ( m1_subset_1 @
% 20.12/20.30                             E @ 
% 20.12/20.30                             ( k1_zfmisc_1 @
% 20.12/20.30                               ( k2_zfmisc_1 @
% 20.12/20.30                                 ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 20.12/20.30                         ( ( ( v1_funct_1 @
% 20.12/20.30                               ( k2_tmap_1 @
% 20.12/20.30                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) ) & 
% 20.12/20.30                             ( v1_funct_2 @
% 20.12/20.30                               ( k2_tmap_1 @
% 20.12/20.30                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.12/20.30                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.12/20.30                               ( u1_struct_0 @ B ) ) & 
% 20.12/20.30                             ( v5_pre_topc @
% 20.12/20.30                               ( k2_tmap_1 @
% 20.12/20.30                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.12/20.30                               ( k1_tsep_1 @ A @ C @ D ) @ B ) & 
% 20.12/20.30                             ( m1_subset_1 @
% 20.12/20.30                               ( k2_tmap_1 @
% 20.12/20.30                                 A @ B @ E @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.12/20.30                               ( k1_zfmisc_1 @
% 20.12/20.30                                 ( k2_zfmisc_1 @
% 20.12/20.30                                   ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 20.12/20.30                                   ( u1_struct_0 @ B ) ) ) ) ) <=>
% 20.12/20.30                           ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ C ) ) & 
% 20.12/20.30                             ( v1_funct_2 @
% 20.12/20.30                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 20.12/20.30                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 20.12/20.30                             ( v5_pre_topc @
% 20.12/20.30                               ( k2_tmap_1 @ A @ B @ E @ C ) @ C @ B ) & 
% 20.12/20.30                             ( m1_subset_1 @
% 20.12/20.30                               ( k2_tmap_1 @ A @ B @ E @ C ) @ 
% 20.12/20.30                               ( k1_zfmisc_1 @
% 20.12/20.30                                 ( k2_zfmisc_1 @
% 20.12/20.30                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 20.12/20.30                             ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ E @ D ) ) & 
% 20.12/20.30                             ( v1_funct_2 @
% 20.12/20.30                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 20.12/20.30                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 20.12/20.30                             ( v5_pre_topc @
% 20.12/20.30                               ( k2_tmap_1 @ A @ B @ E @ D ) @ D @ B ) & 
% 20.12/20.30                             ( m1_subset_1 @
% 20.12/20.30                               ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 20.12/20.30                               ( k1_zfmisc_1 @
% 20.12/20.30                                 ( k2_zfmisc_1 @
% 20.12/20.30                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 20.12/20.30  thf('77', plain,
% 20.12/20.30      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 20.12/20.30         ((v2_struct_0 @ X38)
% 20.12/20.30          | ~ (v2_pre_topc @ X38)
% 20.12/20.30          | ~ (l1_pre_topc @ X38)
% 20.12/20.30          | (v2_struct_0 @ X39)
% 20.12/20.30          | ~ (m1_pre_topc @ X39 @ X40)
% 20.12/20.30          | ~ (v1_funct_1 @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X42))
% 20.12/20.30          | ~ (v1_funct_2 @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X42) @ 
% 20.12/20.30               (u1_struct_0 @ X42) @ (u1_struct_0 @ X38))
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X42) @ X42 @ X38)
% 20.12/20.30          | ~ (m1_subset_1 @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X42) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X38))))
% 20.12/20.30          | ~ (v1_funct_1 @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X39))
% 20.12/20.30          | ~ (v1_funct_2 @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X39) @ 
% 20.12/20.30               (u1_struct_0 @ X39) @ (u1_struct_0 @ X38))
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X39) @ X39 @ X38)
% 20.12/20.30          | ~ (m1_subset_1 @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X39) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38))))
% 20.12/20.30          | (v5_pre_topc @ 
% 20.12/20.30             (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30             (k1_tsep_1 @ X40 @ X42 @ X39) @ X38)
% 20.12/20.30          | ~ (m1_subset_1 @ X41 @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))))
% 20.12/20.30          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))
% 20.12/20.30          | ~ (v1_funct_1 @ X41)
% 20.12/20.30          | ~ (r4_tsep_1 @ X40 @ X42 @ X39)
% 20.12/20.30          | ~ (m1_pre_topc @ X42 @ X40)
% 20.12/20.30          | (v2_struct_0 @ X42)
% 20.12/20.30          | ~ (l1_pre_topc @ X40)
% 20.12/20.30          | ~ (v2_pre_topc @ X40)
% 20.12/20.30          | (v2_struct_0 @ X40))),
% 20.12/20.30      inference('cnf', [status(esa)], [t129_tmap_1])).
% 20.12/20.30  thf('78', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v2_struct_0 @ sk_A)
% 20.12/20.30          | ~ (v2_pre_topc @ sk_A)
% 20.12/20.30          | ~ (l1_pre_topc @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_D)
% 20.12/20.30          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 20.12/20.30          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 20.12/20.30          | ~ (v1_funct_1 @ sk_C)
% 20.12/20.30          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (m1_subset_1 @ sk_C @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30          | (v5_pre_topc @ 
% 20.12/20.30             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 20.12/20.30             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 20.12/20.30          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 20.12/20.30          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.12/20.30               sk_B)
% 20.12/20.30          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.12/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ X0)
% 20.12/20.30          | ~ (l1_pre_topc @ sk_B)
% 20.12/20.30          | ~ (v2_pre_topc @ sk_B)
% 20.12/20.30          | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('sup-', [status(thm)], ['76', '77'])).
% 20.12/20.30  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('81', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('83', plain,
% 20.12/20.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('84', plain,
% 20.12/20.30      ((m1_subset_1 @ sk_C @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('85', plain,
% 20.12/20.30      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | (v1_funct_1 @ sk_C))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('86', plain,
% 20.12/20.30      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 20.12/20.30         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('split', [status(esa)], ['85'])).
% 20.12/20.30  thf('87', plain,
% 20.12/20.30      ((m1_subset_1 @ sk_C @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('88', plain,
% 20.12/20.30      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 20.12/20.30         (~ (m1_subset_1 @ X34 @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36))))
% 20.12/20.30          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36))
% 20.12/20.30          | ~ (v1_funct_1 @ X34)
% 20.12/20.30          | ~ (l1_struct_0 @ X36)
% 20.12/20.30          | ~ (l1_struct_0 @ X35)
% 20.12/20.30          | ~ (l1_struct_0 @ X37)
% 20.12/20.30          | (v1_funct_2 @ (k2_tmap_1 @ X35 @ X36 @ X34 @ X37) @ 
% 20.12/20.30             (u1_struct_0 @ X37) @ (u1_struct_0 @ X36)))),
% 20.12/20.30      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 20.12/20.30  thf('89', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (l1_struct_0 @ X0)
% 20.12/20.30          | ~ (l1_struct_0 @ sk_A)
% 20.12/20.30          | ~ (l1_struct_0 @ sk_B)
% 20.12/20.30          | ~ (v1_funct_1 @ sk_C)
% 20.12/20.30          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['87', '88'])).
% 20.12/20.30  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 20.12/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.12/20.30  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 20.12/20.30      inference('sup-', [status(thm)], ['58', '59'])).
% 20.12/20.30  thf('92', plain, ((v1_funct_1 @ sk_C)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('93', plain,
% 20.12/20.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('94', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 20.12/20.30  thf('95', plain,
% 20.12/20.30      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('split', [status(esa)], ['64'])).
% 20.12/20.30  thf('96', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_D))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('sup-', [status(thm)], ['94', '95'])).
% 20.12/20.30  thf('97', plain, ((l1_struct_0 @ sk_D)),
% 20.12/20.30      inference('sup-', [status(thm)], ['71', '72'])).
% 20.12/20.30  thf('98', plain,
% 20.12/20.30      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 20.12/20.30      inference('demod', [status(thm)], ['96', '97'])).
% 20.12/20.30  thf('99', plain,
% 20.12/20.30      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['98'])).
% 20.12/20.30  thf('100', plain,
% 20.12/20.30      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['86', '99'])).
% 20.12/20.30  thf('101', plain,
% 20.12/20.30      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.12/20.30        | (v1_funct_1 @ sk_C))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('102', plain,
% 20.12/20.30      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 20.12/20.30         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 20.12/20.30      inference('split', [status(esa)], ['101'])).
% 20.12/20.30  thf('103', plain,
% 20.12/20.30      ((m1_subset_1 @ sk_C @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('104', plain,
% 20.12/20.30      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 20.12/20.30         (~ (m1_subset_1 @ X34 @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36))))
% 20.12/20.30          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X36))
% 20.12/20.30          | ~ (v1_funct_1 @ X34)
% 20.12/20.30          | ~ (l1_struct_0 @ X36)
% 20.12/20.30          | ~ (l1_struct_0 @ X35)
% 20.12/20.30          | ~ (l1_struct_0 @ X37)
% 20.12/20.30          | (v1_funct_1 @ (k2_tmap_1 @ X35 @ X36 @ X34 @ X37)))),
% 20.12/20.30      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 20.12/20.30  thf('105', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.12/20.30          | ~ (l1_struct_0 @ X0)
% 20.12/20.30          | ~ (l1_struct_0 @ sk_A)
% 20.12/20.30          | ~ (l1_struct_0 @ sk_B)
% 20.12/20.30          | ~ (v1_funct_1 @ sk_C)
% 20.12/20.30          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['103', '104'])).
% 20.12/20.30  thf('106', plain, ((l1_struct_0 @ sk_A)),
% 20.12/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.12/20.30  thf('107', plain, ((l1_struct_0 @ sk_B)),
% 20.12/20.30      inference('sup-', [status(thm)], ['58', '59'])).
% 20.12/20.30  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('109', plain,
% 20.12/20.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('110', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 20.12/20.30  thf('111', plain,
% 20.12/20.30      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 20.12/20.30         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 20.12/20.30      inference('split', [status(esa)], ['64'])).
% 20.12/20.30  thf('112', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_D))
% 20.12/20.30         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 20.12/20.30      inference('sup-', [status(thm)], ['110', '111'])).
% 20.12/20.30  thf('113', plain, ((l1_struct_0 @ sk_D)),
% 20.12/20.30      inference('sup-', [status(thm)], ['71', '72'])).
% 20.12/20.30  thf('114', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 20.12/20.30      inference('demod', [status(thm)], ['112', '113'])).
% 20.12/20.30  thf('115', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['114'])).
% 20.12/20.30  thf('116', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['102', '115'])).
% 20.12/20.30  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('118', plain, ((v2_pre_topc @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('119', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v2_struct_0 @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_D)
% 20.12/20.30          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 20.12/20.30          | (v5_pre_topc @ 
% 20.12/20.30             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 20.12/20.30             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 20.12/20.30          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 20.12/20.30          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.12/20.30               sk_B)
% 20.12/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ X0)
% 20.12/20.30          | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('demod', [status(thm)],
% 20.12/20.30                ['78', '79', '80', '81', '82', '83', '84', '100', '116', 
% 20.12/20.30                 '117', '118'])).
% 20.12/20.30  thf('120', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('121', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v2_struct_0 @ sk_A)
% 20.12/20.30          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 20.12/20.30              = (k7_relat_1 @ sk_C @ (u1_struct_0 @ X0)))
% 20.12/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('demod', [status(thm)],
% 20.12/20.30                ['12', '13', '14', '15', '16', '21', '22', '23'])).
% 20.12/20.30  thf('122', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_B)
% 20.12/20.30        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.12/20.30            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('sup-', [status(thm)], ['120', '121'])).
% 20.12/20.30  thf('123', plain, (~ (v2_struct_0 @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('124', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_A)
% 20.12/20.30        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.12/20.30            = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D))))),
% 20.12/20.30      inference('clc', [status(thm)], ['122', '123'])).
% 20.12/20.30  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('126', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.12/20.30      inference('clc', [status(thm)], ['124', '125'])).
% 20.12/20.30  thf('127', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 20.12/20.30        | (v1_funct_1 @ sk_C))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('128', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))
% 20.12/20.30         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('split', [status(esa)], ['127'])).
% 20.12/20.30  thf('129', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.12/20.30      inference('clc', [status(thm)], ['124', '125'])).
% 20.12/20.30  thf('130', plain,
% 20.12/20.30      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B))
% 20.12/20.30         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('demod', [status(thm)], ['128', '129'])).
% 20.12/20.30  thf('131', plain,
% 20.12/20.30      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.12/20.30        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('132', plain,
% 20.12/20.30      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 20.12/20.30         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('split', [status(esa)], ['131'])).
% 20.12/20.30  thf('133', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 20.12/20.30  thf('134', plain,
% 20.12/20.30      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_E))),
% 20.12/20.30      inference('simplify', [status(thm)], ['41'])).
% 20.12/20.30  thf('135', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 20.12/20.30  thf('136', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30           (k1_zfmisc_1 @ 
% 20.12/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['54', '57', '60', '61', '62'])).
% 20.12/20.30  thf('137', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('138', plain,
% 20.12/20.30      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 20.12/20.30         ((v2_struct_0 @ X38)
% 20.12/20.30          | ~ (v2_pre_topc @ X38)
% 20.12/20.30          | ~ (l1_pre_topc @ X38)
% 20.12/20.30          | (v2_struct_0 @ X39)
% 20.12/20.30          | ~ (m1_pre_topc @ X39 @ X40)
% 20.12/20.30          | ~ (v1_funct_1 @ 
% 20.12/20.30               (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)))
% 20.12/20.30          | ~ (v1_funct_2 @ 
% 20.12/20.30               (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30               (u1_struct_0 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30               (u1_struct_0 @ X38))
% 20.12/20.30          | ~ (v5_pre_topc @ 
% 20.12/20.30               (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30               (k1_tsep_1 @ X40 @ X42 @ X39) @ X38)
% 20.12/20.30          | ~ (m1_subset_1 @ 
% 20.12/20.30               (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30                 (u1_struct_0 @ X38))))
% 20.12/20.30          | (v5_pre_topc @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X39) @ X39 @ X38)
% 20.12/20.30          | ~ (m1_subset_1 @ X41 @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))))
% 20.12/20.30          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))
% 20.12/20.30          | ~ (v1_funct_1 @ X41)
% 20.12/20.30          | ~ (r4_tsep_1 @ X40 @ X42 @ X39)
% 20.12/20.30          | ~ (m1_pre_topc @ X42 @ X40)
% 20.12/20.30          | (v2_struct_0 @ X42)
% 20.12/20.30          | ~ (l1_pre_topc @ X40)
% 20.12/20.30          | ~ (v2_pre_topc @ X40)
% 20.12/20.30          | (v2_struct_0 @ X40))),
% 20.12/20.30      inference('cnf', [status(esa)], [t129_tmap_1])).
% 20.12/20.30  thf('139', plain,
% 20.12/20.30      (![X0 : $i, X1 : $i]:
% 20.12/20.30         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ 
% 20.12/20.30               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30               (u1_struct_0 @ X0))))
% 20.12/20.30          | (v2_struct_0 @ sk_A)
% 20.12/20.30          | ~ (v2_pre_topc @ sk_A)
% 20.12/20.30          | ~ (l1_pre_topc @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_D)
% 20.12/20.30          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 20.12/20.30          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 20.12/20.30          | ~ (v1_funct_1 @ X1)
% 20.12/20.30          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 20.12/20.30          | ~ (m1_subset_1 @ X1 @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 20.12/20.30          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E) @ sk_E @ X0)
% 20.12/20.30          | ~ (v5_pre_topc @ 
% 20.12/20.30               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 20.12/20.30          | ~ (v1_funct_2 @ 
% 20.12/20.30               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30               (u1_struct_0 @ X0))
% 20.12/20.30          | ~ (v1_funct_1 @ 
% 20.12/20.30               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 20.12/20.30          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_E)
% 20.12/20.30          | ~ (l1_pre_topc @ X0)
% 20.12/20.30          | ~ (v2_pre_topc @ X0)
% 20.12/20.30          | (v2_struct_0 @ X0))),
% 20.12/20.30      inference('sup-', [status(thm)], ['137', '138'])).
% 20.12/20.30  thf('140', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('143', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('144', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('145', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('146', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('147', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('148', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('149', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('150', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('151', plain,
% 20.12/20.30      (![X0 : $i, X1 : $i]:
% 20.12/20.30         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 20.12/20.30          | (v2_struct_0 @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_D)
% 20.12/20.30          | ~ (v1_funct_1 @ X1)
% 20.12/20.30          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 20.12/20.30          | ~ (m1_subset_1 @ X1 @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 20.12/20.30          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_E) @ sk_E @ X0)
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ sk_A @ X0)
% 20.12/20.30          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 20.12/20.30               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 20.12/20.30          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A))
% 20.12/20.30          | (v2_struct_0 @ sk_E)
% 20.12/20.30          | ~ (l1_pre_topc @ X0)
% 20.12/20.30          | ~ (v2_pre_topc @ X0)
% 20.12/20.30          | (v2_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)],
% 20.12/20.30                ['139', '140', '141', '142', '143', '144', '145', '146', 
% 20.12/20.30                 '147', '148', '149', '150'])).
% 20.12/20.30  thf('152', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | ~ (v2_pre_topc @ sk_B)
% 20.12/20.30        | ~ (l1_pre_topc @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 20.12/20.30             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 20.12/20.30        | ~ (m1_subset_1 @ sk_C @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v1_funct_1 @ sk_C)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('sup-', [status(thm)], ['136', '151'])).
% 20.12/20.30  thf('153', plain, ((l1_struct_0 @ sk_A)),
% 20.12/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.12/20.30  thf('154', plain, ((v2_pre_topc @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('155', plain, ((l1_pre_topc @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('156', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('157', plain,
% 20.12/20.30      ((m1_subset_1 @ sk_C @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('158', plain,
% 20.12/20.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('160', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 20.12/20.30             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.12/20.30           sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('demod', [status(thm)],
% 20.12/20.30                ['152', '153', '154', '155', '156', '157', '158', '159'])).
% 20.12/20.30  thf('161', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.12/20.30           sk_B)
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('sup-', [status(thm)], ['135', '160'])).
% 20.12/20.30  thf('162', plain, ((l1_struct_0 @ sk_A)),
% 20.12/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.12/20.30  thf('163', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.12/20.30           sk_B)
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('demod', [status(thm)], ['161', '162'])).
% 20.12/20.30  thf('164', plain,
% 20.12/20.30      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.12/20.30           sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('sup-', [status(thm)], ['134', '163'])).
% 20.12/20.30  thf('165', plain,
% 20.12/20.30      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('simplify', [status(thm)], ['164'])).
% 20.12/20.30  thf('166', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_A)
% 20.12/20.30        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.12/20.30           sk_B))),
% 20.12/20.30      inference('sup-', [status(thm)], ['133', '165'])).
% 20.12/20.30  thf('167', plain, ((l1_struct_0 @ sk_A)),
% 20.12/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.12/20.30  thf('168', plain,
% 20.12/20.30      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.12/20.30           sk_B))),
% 20.12/20.30      inference('demod', [status(thm)], ['166', '167'])).
% 20.12/20.30  thf('169', plain,
% 20.12/20.30      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.12/20.30          sk_B)
% 20.12/20.30         | (v2_struct_0 @ sk_B)
% 20.12/20.30         | (v2_struct_0 @ sk_D)
% 20.12/20.30         | (v2_struct_0 @ sk_A)
% 20.12/20.30         | (v2_struct_0 @ sk_E))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['132', '168'])).
% 20.12/20.30  thf('170', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('171', plain,
% 20.12/20.30      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('split', [status(esa)], ['64'])).
% 20.12/20.30  thf('172', plain,
% 20.12/20.30      ((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ 
% 20.12/20.30           sk_B))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['170', '171'])).
% 20.12/20.30  thf('173', plain,
% 20.12/20.30      ((((v2_struct_0 @ sk_E)
% 20.12/20.30         | (v2_struct_0 @ sk_A)
% 20.12/20.30         | (v2_struct_0 @ sk_D)
% 20.12/20.30         | (v2_struct_0 @ sk_B)))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['169', '172'])).
% 20.12/20.30  thf('174', plain, (~ (v2_struct_0 @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('175', plain,
% 20.12/20.30      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['173', '174'])).
% 20.12/20.30  thf('176', plain, (~ (v2_struct_0 @ sk_D)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('177', plain,
% 20.12/20.30      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('clc', [status(thm)], ['175', '176'])).
% 20.12/20.30  thf('178', plain, (~ (v2_struct_0 @ sk_E)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('179', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_A))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('clc', [status(thm)], ['177', '178'])).
% 20.12/20.30  thf('180', plain, (~ (v2_struct_0 @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('181', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 20.12/20.30       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('sup-', [status(thm)], ['179', '180'])).
% 20.12/20.30  thf('182', plain,
% 20.12/20.30      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 20.12/20.30         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('split', [status(esa)], ['131'])).
% 20.12/20.30  thf('183', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 20.12/20.30  thf('184', plain,
% 20.12/20.30      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) = (sk_C))
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_E))),
% 20.12/20.30      inference('simplify', [status(thm)], ['41'])).
% 20.12/20.30  thf('185', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 20.12/20.30  thf('186', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30           (k1_zfmisc_1 @ 
% 20.12/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['54', '57', '60', '61', '62'])).
% 20.12/20.30  thf('187', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('188', plain,
% 20.12/20.30      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 20.12/20.30         ((v2_struct_0 @ X38)
% 20.12/20.30          | ~ (v2_pre_topc @ X38)
% 20.12/20.30          | ~ (l1_pre_topc @ X38)
% 20.12/20.30          | (v2_struct_0 @ X39)
% 20.12/20.30          | ~ (m1_pre_topc @ X39 @ X40)
% 20.12/20.30          | ~ (v1_funct_1 @ 
% 20.12/20.30               (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)))
% 20.12/20.30          | ~ (v1_funct_2 @ 
% 20.12/20.30               (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30               (u1_struct_0 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30               (u1_struct_0 @ X38))
% 20.12/20.30          | ~ (v5_pre_topc @ 
% 20.12/20.30               (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30               (k1_tsep_1 @ X40 @ X42 @ X39) @ X38)
% 20.12/20.30          | ~ (m1_subset_1 @ 
% 20.12/20.30               (k2_tmap_1 @ X40 @ X38 @ X41 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X40 @ X42 @ X39)) @ 
% 20.12/20.30                 (u1_struct_0 @ X38))))
% 20.12/20.30          | (v5_pre_topc @ (k2_tmap_1 @ X40 @ X38 @ X41 @ X42) @ X42 @ X38)
% 20.12/20.30          | ~ (m1_subset_1 @ X41 @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))))
% 20.12/20.30          | ~ (v1_funct_2 @ X41 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X38))
% 20.12/20.30          | ~ (v1_funct_1 @ X41)
% 20.12/20.30          | ~ (r4_tsep_1 @ X40 @ X42 @ X39)
% 20.12/20.30          | ~ (m1_pre_topc @ X42 @ X40)
% 20.12/20.30          | (v2_struct_0 @ X42)
% 20.12/20.30          | ~ (l1_pre_topc @ X40)
% 20.12/20.30          | ~ (v2_pre_topc @ X40)
% 20.12/20.30          | (v2_struct_0 @ X40))),
% 20.12/20.30      inference('cnf', [status(esa)], [t129_tmap_1])).
% 20.12/20.30  thf('189', plain,
% 20.12/20.30      (![X0 : $i, X1 : $i]:
% 20.12/20.30         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ 
% 20.12/20.30               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30               (u1_struct_0 @ X0))))
% 20.12/20.30          | (v2_struct_0 @ sk_A)
% 20.12/20.30          | ~ (v2_pre_topc @ sk_A)
% 20.12/20.30          | ~ (l1_pre_topc @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_D)
% 20.12/20.30          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 20.12/20.30          | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 20.12/20.30          | ~ (v1_funct_1 @ X1)
% 20.12/20.30          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 20.12/20.30          | ~ (m1_subset_1 @ X1 @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 20.12/20.30          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D) @ sk_D @ X0)
% 20.12/20.30          | ~ (v5_pre_topc @ 
% 20.12/20.30               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30               (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 20.12/20.30          | ~ (v1_funct_2 @ 
% 20.12/20.30               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30               (u1_struct_0 @ X0))
% 20.12/20.30          | ~ (v1_funct_1 @ 
% 20.12/20.30               (k2_tmap_1 @ sk_A @ X0 @ X1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 20.12/20.30          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_E)
% 20.12/20.30          | ~ (l1_pre_topc @ X0)
% 20.12/20.30          | ~ (v2_pre_topc @ X0)
% 20.12/20.30          | (v2_struct_0 @ X0))),
% 20.12/20.30      inference('sup-', [status(thm)], ['187', '188'])).
% 20.12/20.30  thf('190', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('191', plain, ((v2_pre_topc @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('192', plain, ((l1_pre_topc @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('193', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('194', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('195', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('196', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('197', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('198', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('199', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('200', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('201', plain,
% 20.12/20.30      (![X0 : $i, X1 : $i]:
% 20.12/20.30         (~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 20.12/20.30          | (v2_struct_0 @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_D)
% 20.12/20.30          | ~ (v1_funct_1 @ X1)
% 20.12/20.30          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 20.12/20.30          | ~ (m1_subset_1 @ X1 @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 20.12/20.30          | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_D) @ sk_D @ X0)
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ sk_A @ X0)
% 20.12/20.30          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A) @ 
% 20.12/20.30               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 20.12/20.30          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ X0 @ X1 @ sk_A))
% 20.12/20.30          | (v2_struct_0 @ sk_E)
% 20.12/20.30          | ~ (l1_pre_topc @ X0)
% 20.12/20.30          | ~ (v2_pre_topc @ X0)
% 20.12/20.30          | (v2_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)],
% 20.12/20.30                ['189', '190', '191', '192', '193', '194', '195', '196', 
% 20.12/20.30                 '197', '198', '199', '200'])).
% 20.12/20.30  thf('202', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | ~ (v2_pre_topc @ sk_B)
% 20.12/20.30        | ~ (l1_pre_topc @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 20.12/20.30             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 20.12/20.30        | ~ (m1_subset_1 @ sk_C @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v1_funct_1 @ sk_C)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('sup-', [status(thm)], ['186', '201'])).
% 20.12/20.30  thf('203', plain, ((l1_struct_0 @ sk_A)),
% 20.12/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.12/20.30  thf('204', plain, ((v2_pre_topc @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('205', plain, ((l1_pre_topc @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('206', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.12/20.30      inference('clc', [status(thm)], ['124', '125'])).
% 20.12/20.30  thf('207', plain,
% 20.12/20.30      ((m1_subset_1 @ sk_C @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('208', plain,
% 20.12/20.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('210', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ 
% 20.12/20.30             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.12/20.30           sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('demod', [status(thm)],
% 20.12/20.30                ['202', '203', '204', '205', '206', '207', '208', '209'])).
% 20.12/20.30  thf('211', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.12/20.30           sk_B)
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('sup-', [status(thm)], ['185', '210'])).
% 20.12/20.30  thf('212', plain, ((l1_struct_0 @ sk_A)),
% 20.12/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.12/20.30  thf('213', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.12/20.30           sk_B)
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('demod', [status(thm)], ['211', '212'])).
% 20.12/20.30  thf('214', plain,
% 20.12/20.30      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.12/20.30           sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('sup-', [status(thm)], ['184', '213'])).
% 20.12/20.30  thf('215', plain,
% 20.12/20.30      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A))
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('simplify', [status(thm)], ['214'])).
% 20.12/20.30  thf('216', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_A)
% 20.12/20.30        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.12/20.30           sk_B))),
% 20.12/20.30      inference('sup-', [status(thm)], ['183', '215'])).
% 20.12/20.30  thf('217', plain, ((l1_struct_0 @ sk_A)),
% 20.12/20.30      inference('sup-', [status(thm)], ['55', '56'])).
% 20.12/20.30  thf('218', plain,
% 20.12/20.30      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.12/20.30           sk_B))),
% 20.12/20.30      inference('demod', [status(thm)], ['216', '217'])).
% 20.12/20.30  thf('219', plain,
% 20.12/20.30      ((((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.12/20.30          sk_B)
% 20.12/20.30         | (v2_struct_0 @ sk_B)
% 20.12/20.30         | (v2_struct_0 @ sk_D)
% 20.12/20.30         | (v2_struct_0 @ sk_A)
% 20.12/20.30         | (v2_struct_0 @ sk_E))) <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['182', '218'])).
% 20.12/20.30  thf('220', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)))),
% 20.12/20.30      inference('clc', [status(thm)], ['124', '125'])).
% 20.12/20.30  thf('221', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 20.12/20.30        | (v1_funct_1 @ sk_C))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('222', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 20.12/20.30         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('split', [status(esa)], ['221'])).
% 20.12/20.30  thf('223', plain,
% 20.12/20.30      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30           (k1_zfmisc_1 @ 
% 20.12/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 20.12/20.30        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30             (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))
% 20.12/20.30        | ~ (m1_subset_1 @ sk_C @ 
% 20.12/20.30             (k1_zfmisc_1 @ 
% 20.12/20.30              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v1_funct_1 @ sk_C))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('224', plain,
% 20.12/20.30      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30         (k1_zfmisc_1 @ 
% 20.12/20.30          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30        | (v1_funct_1 @ sk_C))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('225', plain,
% 20.12/20.30      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30         (k1_zfmisc_1 @ 
% 20.12/20.30          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 20.12/20.30         <= (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 20.12/20.30      inference('split', [status(esa)], ['224'])).
% 20.12/20.30  thf('226', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30           (k1_zfmisc_1 @ 
% 20.12/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['54', '57', '60', '61', '62'])).
% 20.12/20.30  thf('227', plain,
% 20.12/20.30      ((~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30           (k1_zfmisc_1 @ 
% 20.12/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))
% 20.12/20.30         <= (~
% 20.12/20.30             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 20.12/20.30      inference('split', [status(esa)], ['64'])).
% 20.12/20.30  thf('228', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_E))
% 20.12/20.30         <= (~
% 20.12/20.30             ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))))),
% 20.12/20.30      inference('sup-', [status(thm)], ['226', '227'])).
% 20.12/20.30  thf('229', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('230', plain,
% 20.12/20.30      (![X25 : $i, X26 : $i]:
% 20.12/20.30         (~ (m1_pre_topc @ X25 @ X26)
% 20.12/20.30          | (l1_pre_topc @ X25)
% 20.12/20.30          | ~ (l1_pre_topc @ X26))),
% 20.12/20.30      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 20.12/20.30  thf('231', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_E))),
% 20.12/20.30      inference('sup-', [status(thm)], ['229', '230'])).
% 20.12/20.30  thf('232', plain, ((l1_pre_topc @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('233', plain, ((l1_pre_topc @ sk_E)),
% 20.12/20.30      inference('demod', [status(thm)], ['231', '232'])).
% 20.12/20.30  thf('234', plain,
% 20.12/20.30      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 20.12/20.30      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 20.12/20.30  thf('235', plain, ((l1_struct_0 @ sk_E)),
% 20.12/20.30      inference('sup-', [status(thm)], ['233', '234'])).
% 20.12/20.30  thf('236', plain,
% 20.12/20.30      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30         (k1_zfmisc_1 @ 
% 20.12/20.30          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 20.12/20.30      inference('demod', [status(thm)], ['228', '235'])).
% 20.12/20.30  thf('237', plain,
% 20.12/20.30      (((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30         (k1_zfmisc_1 @ 
% 20.12/20.30          (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['236'])).
% 20.12/20.30  thf('238', plain,
% 20.12/20.30      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['225', '237'])).
% 20.12/20.30  thf('239', plain,
% 20.12/20.30      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | (v1_funct_1 @ sk_C))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('240', plain,
% 20.12/20.30      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 20.12/20.30         <= (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('split', [status(esa)], ['239'])).
% 20.12/20.30  thf('241', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['89', '90', '91', '92', '93'])).
% 20.12/20.30  thf('242', plain,
% 20.12/20.30      ((~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30           (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('split', [status(esa)], ['64'])).
% 20.12/20.30  thf('243', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_E))
% 20.12/20.30         <= (~
% 20.12/20.30             ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30               (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('sup-', [status(thm)], ['241', '242'])).
% 20.12/20.30  thf('244', plain, ((l1_struct_0 @ sk_E)),
% 20.12/20.30      inference('sup-', [status(thm)], ['233', '234'])).
% 20.12/20.30  thf('245', plain,
% 20.12/20.30      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 20.12/20.30      inference('demod', [status(thm)], ['243', '244'])).
% 20.12/20.30  thf('246', plain,
% 20.12/20.30      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30         (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B)))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['245'])).
% 20.12/20.30  thf('247', plain,
% 20.12/20.30      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['240', '246'])).
% 20.12/20.30  thf('248', plain,
% 20.12/20.30      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 20.12/20.30        | (v1_funct_1 @ sk_C))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('249', plain,
% 20.12/20.30      (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 20.12/20.30         <= (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 20.12/20.30      inference('split', [status(esa)], ['248'])).
% 20.12/20.30  thf('250', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.12/20.30          | ~ (l1_struct_0 @ X0))),
% 20.12/20.30      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 20.12/20.30  thf('251', plain,
% 20.12/20.30      ((~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 20.12/20.30         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 20.12/20.30      inference('split', [status(esa)], ['64'])).
% 20.12/20.30  thf('252', plain,
% 20.12/20.30      ((~ (l1_struct_0 @ sk_E))
% 20.12/20.30         <= (~ ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))))),
% 20.12/20.30      inference('sup-', [status(thm)], ['250', '251'])).
% 20.12/20.30  thf('253', plain, ((l1_struct_0 @ sk_E)),
% 20.12/20.30      inference('sup-', [status(thm)], ['233', '234'])).
% 20.12/20.30  thf('254', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 20.12/20.30      inference('demod', [status(thm)], ['252', '253'])).
% 20.12/20.30  thf('255', plain, (((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['254'])).
% 20.12/20.30  thf('256', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['249', '255'])).
% 20.12/20.30  thf('257', plain,
% 20.12/20.30      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['51', '75'])).
% 20.12/20.30  thf('258', plain,
% 20.12/20.30      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 20.12/20.30        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['86', '99'])).
% 20.12/20.30  thf('259', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['102', '115'])).
% 20.12/20.30  thf('260', plain,
% 20.12/20.30      ((m1_subset_1 @ sk_C @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('261', plain,
% 20.12/20.30      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('262', plain, ((v1_funct_1 @ sk_C)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('263', plain,
% 20.12/20.30      ((~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('demod', [status(thm)],
% 20.12/20.30                ['223', '238', '247', '256', '257', '258', '259', '260', 
% 20.12/20.30                 '261', '262'])).
% 20.12/20.30  thf('264', plain,
% 20.12/20.30      (((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30         | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ 
% 20.12/20.30              sk_B)))
% 20.12/20.30         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['222', '263'])).
% 20.12/20.30  thf('265', plain,
% 20.12/20.30      (((~ (v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ 
% 20.12/20.30            sk_B)
% 20.12/20.30         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 20.12/20.30         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['220', '264'])).
% 20.12/20.30  thf('266', plain,
% 20.12/20.30      ((((v2_struct_0 @ sk_E)
% 20.12/20.30         | (v2_struct_0 @ sk_A)
% 20.12/20.30         | (v2_struct_0 @ sk_D)
% 20.12/20.30         | (v2_struct_0 @ sk_B)
% 20.12/20.30         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)))
% 20.12/20.30         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['219', '265'])).
% 20.12/20.30  thf('267', plain,
% 20.12/20.30      (((v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 20.12/20.30         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('split', [status(esa)], ['131'])).
% 20.12/20.30  thf('268', plain,
% 20.12/20.30      ((((v2_struct_0 @ sk_E)
% 20.12/20.30         | (v2_struct_0 @ sk_A)
% 20.12/20.30         | (v2_struct_0 @ sk_D)
% 20.12/20.30         | (v2_struct_0 @ sk_B)))
% 20.12/20.30         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('demod', [status(thm)], ['266', '267'])).
% 20.12/20.30  thf('269', plain, (~ (v2_struct_0 @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('270', plain,
% 20.12/20.30      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E)))
% 20.12/20.30         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('sup-', [status(thm)], ['268', '269'])).
% 20.12/20.30  thf('271', plain, (~ (v2_struct_0 @ sk_D)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('272', plain,
% 20.12/20.30      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A)))
% 20.12/20.30         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('clc', [status(thm)], ['270', '271'])).
% 20.12/20.30  thf('273', plain, (~ (v2_struct_0 @ sk_E)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('274', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_A))
% 20.12/20.30         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B)) & 
% 20.12/20.30             ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('clc', [status(thm)], ['272', '273'])).
% 20.12/20.30  thf('275', plain, (~ (v2_struct_0 @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('276', plain,
% 20.12/20.30      (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)) | 
% 20.12/20.30       ~
% 20.12/20.30       ((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 20.12/20.30      inference('sup-', [status(thm)], ['274', '275'])).
% 20.12/20.30  thf('277', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)
% 20.12/20.30        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('278', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B)) | 
% 20.12/20.30       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('split', [status(esa)], ['277'])).
% 20.12/20.30  thf('279', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_D @ sk_B))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['181', '276', '278'])).
% 20.12/20.30  thf('280', plain,
% 20.12/20.30      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_D)) @ sk_D @ sk_B)),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['130', '279'])).
% 20.12/20.30  thf('281', plain,
% 20.12/20.30      (![X0 : $i]:
% 20.12/20.30         ((v2_struct_0 @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ sk_D)
% 20.12/20.30          | ~ (r4_tsep_1 @ sk_A @ sk_D @ X0)
% 20.12/20.30          | (v5_pre_topc @ 
% 20.12/20.30             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ X0)) @ 
% 20.12/20.30             (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_B)
% 20.12/20.30          | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30               (k1_zfmisc_1 @ 
% 20.12/20.30                (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30          | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ X0 @ sk_B)
% 20.12/20.30          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 20.12/20.30               (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 20.12/20.30          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0))
% 20.12/20.30          | ~ (m1_pre_topc @ X0 @ sk_A)
% 20.12/20.30          | (v2_struct_0 @ X0)
% 20.12/20.30          | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('demod', [status(thm)], ['119', '126', '280'])).
% 20.12/20.30  thf('282', plain,
% 20.12/20.30      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.12/20.30           (k1_zfmisc_1 @ 
% 20.12/20.30            (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | ~ (m1_pre_topc @ sk_E @ sk_A)
% 20.12/20.30        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 20.12/20.30        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30             (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))
% 20.12/20.30        | ~ (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30             sk_B)
% 20.12/20.30        | (v5_pre_topc @ 
% 20.12/20.30           (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 20.12/20.30           (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_B)
% 20.12/20.30        | ~ (r4_tsep_1 @ sk_A @ sk_D @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('sup-', [status(thm)], ['49', '281'])).
% 20.12/20.30  thf('283', plain,
% 20.12/20.30      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['225', '237'])).
% 20.12/20.30  thf('284', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('285', plain,
% 20.12/20.30      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.12/20.30        (k1_zfmisc_1 @ 
% 20.12/20.30         (k2_zfmisc_1 @ (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))))),
% 20.12/20.30      inference('demod', [status(thm)], ['283', '284'])).
% 20.12/20.30  thf('286', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('287', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('288', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['249', '255'])).
% 20.12/20.30  thf('289', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('290', plain,
% 20.12/20.30      ((v1_funct_1 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('demod', [status(thm)], ['288', '289'])).
% 20.12/20.30  thf('291', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('292', plain,
% 20.12/20.30      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 20.12/20.30        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['240', '246'])).
% 20.12/20.30  thf('293', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('294', plain,
% 20.12/20.30      ((v1_funct_2 @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ 
% 20.12/20.30        (u1_struct_0 @ sk_E) @ (u1_struct_0 @ sk_B))),
% 20.12/20.30      inference('demod', [status(thm)], ['292', '293'])).
% 20.12/20.30  thf('295', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('296', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))
% 20.12/20.30         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('split', [status(esa)], ['221'])).
% 20.12/20.30  thf('297', plain,
% 20.12/20.30      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 20.12/20.30         = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)))),
% 20.12/20.30      inference('clc', [status(thm)], ['47', '48'])).
% 20.12/20.30  thf('298', plain,
% 20.12/20.30      (((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B))
% 20.12/20.30         <= (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ 
% 20.12/20.30               sk_B)))),
% 20.12/20.30      inference('demod', [status(thm)], ['296', '297'])).
% 20.12/20.30  thf('299', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)
% 20.12/20.30        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('300', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B)) | 
% 20.12/20.30       ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('split', [status(esa)], ['299'])).
% 20.12/20.30  thf('301', plain,
% 20.12/20.30      (((v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_E @ sk_B))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['181', '276', '300'])).
% 20.12/20.30  thf('302', plain,
% 20.12/20.30      ((v5_pre_topc @ (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_E)) @ sk_E @ sk_B)),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['298', '301'])).
% 20.12/20.30  thf('303', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('304', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('305', plain, ((r4_tsep_1 @ sk_A @ sk_D @ sk_E)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('306', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v5_pre_topc @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_A) @ sk_A @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('demod', [status(thm)],
% 20.12/20.30                ['282', '285', '286', '287', '290', '291', '294', '295', 
% 20.12/20.30                 '302', '303', '304', '305'])).
% 20.12/20.30  thf('307', plain,
% 20.12/20.30      (((v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('sup+', [status(thm)], ['42', '306'])).
% 20.12/20.30  thf('308', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_B)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_E)
% 20.12/20.30        | (v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('simplify', [status(thm)], ['307'])).
% 20.12/20.30  thf('309', plain,
% 20.12/20.30      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B))
% 20.12/20.30         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B)))),
% 20.12/20.30      inference('split', [status(esa)], ['64'])).
% 20.12/20.30  thf('310', plain, (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B))),
% 20.12/20.30      inference('sat_resolution*', [status(thm)], ['181', '276'])).
% 20.12/20.30  thf('311', plain, (~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 20.12/20.30      inference('simpl_trail', [status(thm)], ['309', '310'])).
% 20.12/20.30  thf('312', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_E)
% 20.12/20.30        | (v2_struct_0 @ sk_A)
% 20.12/20.30        | (v2_struct_0 @ sk_D)
% 20.12/20.30        | (v2_struct_0 @ sk_B))),
% 20.12/20.30      inference('sup-', [status(thm)], ['308', '311'])).
% 20.12/20.30  thf('313', plain, (~ (v2_struct_0 @ sk_B)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('314', plain,
% 20.12/20.30      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_E))),
% 20.12/20.30      inference('sup-', [status(thm)], ['312', '313'])).
% 20.12/20.30  thf('315', plain, (~ (v2_struct_0 @ sk_D)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('316', plain, (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_A))),
% 20.12/20.30      inference('clc', [status(thm)], ['314', '315'])).
% 20.12/20.30  thf('317', plain, (~ (v2_struct_0 @ sk_E)),
% 20.12/20.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.12/20.30  thf('318', plain, ((v2_struct_0 @ sk_A)),
% 20.12/20.30      inference('clc', [status(thm)], ['316', '317'])).
% 20.12/20.30  thf('319', plain, ($false), inference('demod', [status(thm)], ['0', '318'])).
% 20.12/20.30  
% 20.12/20.30  % SZS output end Refutation
% 20.12/20.30  
% 20.12/20.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
