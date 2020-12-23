%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pdz2Y9p2k3

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 188 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          : 1073 (5125 expanded)
%              Number of equality atoms :   30 ( 102 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t61_tmap_1,conjecture,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                       => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                          = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) )).

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
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                       => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                         => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                            = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_E )
        = ( k9_relat_1 @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ X19 @ X20 @ X21 @ X22 ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 )
        = ( k9_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('13',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ~ ( m1_pre_topc @ X30 @ X32 )
      | ( r1_tarski @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_partfun1 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( r1_tarski @ ( k7_relset_1 @ X15 @ X16 @ X14 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t178_funct_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 )
        = ( k7_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27','32','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( ( k7_relset_1 @ X7 @ X8 @ X6 @ X9 )
        = ( k9_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('45',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( ( k2_tmap_1 @ X27 @ X25 @ X28 @ X26 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X25 ) @ X28 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51','52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['42','59'])).

thf('61',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','60'])).

thf('62',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('64',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('68',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('71',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['0','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pdz2Y9p2k3
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 74 iterations in 0.048s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(t61_tmap_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.51             ( l1_pre_topc @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.51                     ( v1_funct_2 @
% 0.22/0.51                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                     ( m1_subset_1 @
% 0.22/0.51                       D @ 
% 0.22/0.51                       ( k1_zfmisc_1 @
% 0.22/0.51                         ( k2_zfmisc_1 @
% 0.22/0.51                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.51                   ( ![E:$i]:
% 0.22/0.51                     ( ( m1_subset_1 @
% 0.22/0.51                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                       ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.51                         ( ( k7_relset_1 @
% 0.22/0.51                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) =
% 0.22/0.51                           ( k7_relset_1 @
% 0.22/0.51                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.51                             ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
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
% 0.22/0.51                    ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.51                        ( v1_funct_2 @
% 0.22/0.51                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.51                        ( m1_subset_1 @
% 0.22/0.51                          D @ 
% 0.22/0.51                          ( k1_zfmisc_1 @
% 0.22/0.51                            ( k2_zfmisc_1 @
% 0.22/0.51                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.51                      ( ![E:$i]:
% 0.22/0.51                        ( ( m1_subset_1 @
% 0.22/0.51                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                          ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.22/0.51                            ( ( k7_relset_1 @
% 0.22/0.51                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.51                                D @ E ) =
% 0.22/0.51                              ( k7_relset_1 @
% 0.22/0.51                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.51                                ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t61_tmap_1])).
% 0.22/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t162_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ![B:$i,C:$i]:
% 0.22/0.51         ( ( r1_tarski @ B @ C ) =>
% 0.22/0.51           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.22/0.51             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.51          | ((k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.22/0.51              = (k9_relat_1 @ X2 @ X0))
% 0.22/0.51          | ~ (v1_relat_1 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E)
% 0.22/0.51              = (k9_relat_1 @ X0 @ sk_E)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_D @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t44_funct_2, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.51       ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.51         ((r1_tarski @ (k7_relset_1 @ X19 @ X20 @ X21 @ X22) @ X20)
% 0.22/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.22/0.51          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.22/0.51          | ~ (v1_funct_1 @ X21))),
% 0.22/0.51      inference('cnf', [status(esa)], [t44_funct_2])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_funct_1 @ sk_D)
% 0.22/0.51          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.51          | (r1_tarski @ 
% 0.22/0.51             (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51              sk_D @ X0) @ 
% 0.22/0.51             (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_D @ 
% 0.22/0.51        (k1_zfmisc_1 @ 
% 0.22/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.22/0.51          | ((k7_relset_1 @ X7 @ X8 @ X6 @ X9) = (k9_relat_1 @ X6 @ X9)))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.51           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.22/0.51  thf(t2_tsep_1, axiom,
% 0.22/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.22/0.51      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.51  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_B)),
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
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X30 @ X31)
% 0.22/0.51          | ~ (m1_pre_topc @ X30 @ X32)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X32))
% 0.22/0.51          | ~ (m1_pre_topc @ X32 @ X31)
% 0.22/0.51          | ~ (l1_pre_topc @ X31)
% 0.22/0.51          | ~ (v2_pre_topc @ X31))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v2_pre_topc @ sk_B)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('18', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.52        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.22/0.52        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '19'])).
% 0.22/0.52  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t178_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.22/0.52       ( ![E:$i]:
% 0.22/0.52         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.22/0.52             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.22/0.52           ( ( ( r1_tarski @ B @ A ) & 
% 0.22/0.52               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.22/0.52             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.22/0.52               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.22/0.52               ( m1_subset_1 @
% 0.22/0.52                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.22/0.52                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X14)
% 0.22/0.52          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.22/0.52          | (m1_subset_1 @ (k2_partfun1 @ X15 @ X16 @ X14 @ X17) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.22/0.52          | ~ (r1_tarski @ (k7_relset_1 @ X15 @ X16 @ X14 @ X17) @ X18)
% 0.22/0.52          | ~ (r1_tarski @ X17 @ X15)
% 0.22/0.52          | (v1_xboole_0 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t178_funct_2])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.52          | ~ (r1_tarski @ 
% 0.22/0.52               (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                sk_D @ X0) @ 
% 0.22/0.52               X1)
% 0.22/0.52          | (m1_subset_1 @ 
% 0.22/0.52             (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              sk_D @ X0) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(redefinition_k2_partfun1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.22/0.52          | ~ (v1_funct_1 @ X10)
% 0.22/0.52          | ((k2_partfun1 @ X11 @ X12 @ X10 @ X13) = (k7_relat_1 @ X10 @ X13)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.52          | ~ (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ X1)
% 0.22/0.52          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.22/0.52      inference('demod', [status(thm)], ['26', '27', '32', '33', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.22/0.52          | ~ (r1_tarski @ (k9_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)
% 0.22/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '35'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.22/0.52          | ((k7_relset_1 @ X7 @ X8 @ X6 @ X9) = (k9_relat_1 @ X6 @ X9)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ((k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52              (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)
% 0.22/0.52              = (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52         sk_E)
% 0.22/0.52         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (((k9_relat_1 @ sk_D @ sk_E)
% 0.22/0.52         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.22/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d4_tmap_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.52                 ( m1_subset_1 @
% 0.22/0.52                   C @ 
% 0.22/0.52                   ( k1_zfmisc_1 @
% 0.22/0.52                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.52                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.22/0.52                     ( k2_partfun1 @
% 0.22/0.52                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.52                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X25)
% 0.22/0.52          | ~ (v2_pre_topc @ X25)
% 0.22/0.52          | ~ (l1_pre_topc @ X25)
% 0.22/0.52          | ~ (m1_pre_topc @ X26 @ X27)
% 0.22/0.52          | ((k2_tmap_1 @ X27 @ X25 @ X28 @ X26)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X25) @ 
% 0.22/0.52                 X28 @ (u1_struct_0 @ X26)))
% 0.22/0.52          | ~ (m1_subset_1 @ X28 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X25))))
% 0.22/0.52          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X25))
% 0.22/0.52          | ~ (v1_funct_1 @ X28)
% 0.22/0.52          | ~ (l1_pre_topc @ X27)
% 0.22/0.52          | ~ (v2_pre_topc @ X27)
% 0.22/0.52          | (v2_struct_0 @ X27))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_B)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                 sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_B)
% 0.22/0.52          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.52              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.52          | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['46', '47', '48', '49', '50', '51', '52', '53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.52            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.22/0.52        | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['43', '54'])).
% 0.22/0.52  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.52            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.22/0.52      inference('clc', [status(thm)], ['55', '56'])).
% 0.22/0.52  thf('58', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.52         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('clc', [status(thm)], ['57', '58'])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      (((k9_relat_1 @ sk_D @ sk_E)
% 0.22/0.52         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '59'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_D @ sk_E)
% 0.22/0.52          != (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '60'])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_D)
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '61'])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( v1_relat_1 @ C ) ))).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((v1_relat_1 @ X3)
% 0.22/0.52          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.52  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['62', '65'])).
% 0.22/0.52  thf('67', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['66'])).
% 0.22/0.52  thf(fc2_struct_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      (![X24 : $i]:
% 0.22/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.22/0.52          | ~ (l1_struct_0 @ X24)
% 0.22/0.52          | (v2_struct_0 @ X24))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.52  thf('69', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.52  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_l1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.52  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.52  thf('73', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['69', '72'])).
% 0.22/0.52  thf('74', plain, ($false), inference('demod', [status(thm)], ['0', '73'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
