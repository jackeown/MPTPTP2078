%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xEx7FcdkMs

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:47 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 134 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  805 (3071 expanded)
%              Number of equality atoms :   26 (  63 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    r1_tarski @ sk_E @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X8 @ X7 ) @ X6 )
        = ( k9_relat_1 @ X8 @ X6 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_E )
        = ( k9_relat_1 @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k7_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k9_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( ( k2_tmap_1 @ X30 @ X28 @ X31 @ X29 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) @ X31 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k2_partfun1 @ X25 @ X26 @ X24 @ X27 )
        = ( k7_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','20','21','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k7_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k9_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      = ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['7','28','49'])).

thf('51',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('53',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k9_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xEx7FcdkMs
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 154 iterations in 0.129s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.58  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.58  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.58  thf(t61_tmap_1, conjecture,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.58             ( l1_pre_topc @ B ) ) =>
% 0.36/0.58           ( ![C:$i]:
% 0.36/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.36/0.58               ( ![D:$i]:
% 0.36/0.58                 ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.58                     ( v1_funct_2 @
% 0.36/0.58                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.58                     ( m1_subset_1 @
% 0.36/0.58                       D @ 
% 0.36/0.58                       ( k1_zfmisc_1 @
% 0.36/0.58                         ( k2_zfmisc_1 @
% 0.36/0.58                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.58                   ( ![E:$i]:
% 0.36/0.58                     ( ( m1_subset_1 @
% 0.36/0.58                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.58                       ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.58                         ( ( k7_relset_1 @
% 0.36/0.58                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) =
% 0.36/0.58                           ( k7_relset_1 @
% 0.36/0.58                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.58                             ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i]:
% 0.36/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.58            ( l1_pre_topc @ A ) ) =>
% 0.36/0.58          ( ![B:$i]:
% 0.36/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.58                ( l1_pre_topc @ B ) ) =>
% 0.36/0.58              ( ![C:$i]:
% 0.36/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.36/0.58                  ( ![D:$i]:
% 0.36/0.58                    ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.58                        ( v1_funct_2 @
% 0.36/0.58                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.58                        ( m1_subset_1 @
% 0.36/0.58                          D @ 
% 0.36/0.58                          ( k1_zfmisc_1 @
% 0.36/0.58                            ( k2_zfmisc_1 @
% 0.36/0.58                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.58                      ( ![E:$i]:
% 0.36/0.58                        ( ( m1_subset_1 @
% 0.36/0.58                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.58                          ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.36/0.58                            ( ( k7_relset_1 @
% 0.36/0.58                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.58                                D @ E ) =
% 0.36/0.58                              ( k7_relset_1 @
% 0.36/0.58                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.58                                ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t61_tmap_1])).
% 0.36/0.58  thf('0', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t162_relat_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ A ) =>
% 0.36/0.58       ( ![B:$i,C:$i]:
% 0.36/0.58         ( ( r1_tarski @ B @ C ) =>
% 0.36/0.58           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.36/0.58             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.58         (~ (r1_tarski @ X6 @ X7)
% 0.36/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X8 @ X7) @ X6)
% 0.36/0.58              = (k9_relat_1 @ X8 @ X6))
% 0.36/0.58          | ~ (v1_relat_1 @ X8))),
% 0.36/0.58      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X0)
% 0.36/0.58          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E)
% 0.36/0.58              = (k9_relat_1 @ X0 @ sk_E)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.58         sk_E)
% 0.36/0.58         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_D @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(redefinition_k7_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.36/0.58          | ((k7_relset_1 @ X17 @ X18 @ X16 @ X19) = (k9_relat_1 @ X16 @ X19)))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.58           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (((k9_relat_1 @ sk_D @ sk_E)
% 0.36/0.58         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.36/0.58      inference('demod', [status(thm)], ['3', '6'])).
% 0.36/0.58  thf('8', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_D @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(d4_tmap_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.58             ( l1_pre_topc @ B ) ) =>
% 0.36/0.58           ( ![C:$i]:
% 0.36/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.58                 ( m1_subset_1 @
% 0.36/0.58                   C @ 
% 0.36/0.58                   ( k1_zfmisc_1 @
% 0.36/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.58               ( ![D:$i]:
% 0.36/0.58                 ( ( m1_pre_topc @ D @ A ) =>
% 0.36/0.58                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.36/0.58                     ( k2_partfun1 @
% 0.36/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.58                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.58         ((v2_struct_0 @ X28)
% 0.36/0.58          | ~ (v2_pre_topc @ X28)
% 0.36/0.58          | ~ (l1_pre_topc @ X28)
% 0.36/0.58          | ~ (m1_pre_topc @ X29 @ X30)
% 0.36/0.58          | ((k2_tmap_1 @ X30 @ X28 @ X31 @ X29)
% 0.36/0.58              = (k2_partfun1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28) @ 
% 0.36/0.58                 X31 @ (u1_struct_0 @ X29)))
% 0.36/0.58          | ~ (m1_subset_1 @ X31 @ 
% 0.36/0.58               (k1_zfmisc_1 @ 
% 0.36/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))))
% 0.36/0.58          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))
% 0.36/0.58          | ~ (v1_funct_1 @ X31)
% 0.36/0.58          | ~ (l1_pre_topc @ X30)
% 0.36/0.58          | ~ (v2_pre_topc @ X30)
% 0.36/0.58          | (v2_struct_0 @ X30))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((v2_struct_0 @ sk_B)
% 0.36/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.58          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.58          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.36/0.58          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.36/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                 sk_D @ (u1_struct_0 @ X0)))
% 0.36/0.58          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.58          | (v2_struct_0 @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf('12', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('13', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_D @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(redefinition_k2_partfun1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.58     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.58       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.36/0.58          | ~ (v1_funct_1 @ X24)
% 0.36/0.58          | ((k2_partfun1 @ X25 @ X26 @ X24 @ X27) = (k7_relat_1 @ X24 @ X27)))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.58            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.36/0.58          | ~ (v1_funct_1 @ sk_D))),
% 0.36/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.58  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.58           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.58  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((v2_struct_0 @ sk_B)
% 0.36/0.58          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.36/0.58              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.36/0.58          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.58          | (v2_struct_0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)],
% 0.36/0.58                ['11', '12', '13', '14', '15', '20', '21', '22'])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (((v2_struct_0 @ sk_A)
% 0.36/0.58        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.58            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.36/0.58        | (v2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['8', '23'])).
% 0.36/0.58  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (((v2_struct_0 @ sk_B)
% 0.36/0.58        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.58            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.36/0.58      inference('clc', [status(thm)], ['24', '25'])).
% 0.36/0.58  thf('27', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.58         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.36/0.58      inference('clc', [status(thm)], ['26', '27'])).
% 0.36/0.58  thf(t87_relat_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ B ) =>
% 0.36/0.58       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i]:
% 0.36/0.58         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X9 @ X10)) @ X10)
% 0.36/0.58          | ~ (v1_relat_1 @ X9))),
% 0.36/0.58      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_D @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t3_subset, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (![X3 : $i, X4 : $i]:
% 0.36/0.58         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      ((r1_tarski @ sk_D @ 
% 0.36/0.58        (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.58  thf(t88_relat_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X11 : $i, X12 : $i]:
% 0.36/0.58         ((r1_tarski @ (k7_relat_1 @ X11 @ X12) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.36/0.58  thf(t1_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.58       ( r1_tarski @ A @ C ) ))).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.58          | ~ (r1_tarski @ X1 @ X2)
% 0.36/0.58          | (r1_tarski @ X0 @ X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X0)
% 0.36/0.58          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.36/0.58          | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.36/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.36/0.58          | ~ (v1_relat_1 @ sk_D))),
% 0.36/0.58      inference('sup-', [status(thm)], ['32', '35'])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_D @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(cc1_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( v1_relat_1 @ C ) ))).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.58         ((v1_relat_1 @ X13)
% 0.36/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.36/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.58  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.36/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('demod', [status(thm)], ['36', '39'])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (![X3 : $i, X5 : $i]:
% 0.36/0.58         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.36/0.58          (k1_zfmisc_1 @ 
% 0.36/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.58  thf(t13_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.36/0.58       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.36/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.58         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.36/0.58          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.36/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.36/0.58      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.36/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.58          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ sk_D)
% 0.36/0.58          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.36/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['29', '44'])).
% 0.36/0.58  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.58  thf('47', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.36/0.58          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.36/0.58          | ((k7_relset_1 @ X17 @ X18 @ X16 @ X19) = (k9_relat_1 @ X16 @ X19)))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k7_relset_1 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58           (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.36/0.58           = (k9_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      (((k9_relat_1 @ sk_D @ sk_E)
% 0.36/0.58         != (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.36/0.58      inference('demod', [status(thm)], ['7', '28', '49'])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.36/0.58        | ~ (v1_relat_1 @ sk_D))),
% 0.36/0.58      inference('sup-', [status(thm)], ['2', '50'])).
% 0.36/0.58  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.58  thf('53', plain,
% 0.36/0.58      (((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))),
% 0.36/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.36/0.58  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
