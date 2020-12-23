%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HpHdgSewOk

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:46 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 205 expanded)
%              Number of leaves         :   43 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          : 1150 (5090 expanded)
%              Number of equality atoms :   31 (  99 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X9 @ X8 ) @ X7 )
        = ( k9_relat_1 @ X9 @ X7 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v5_relat_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t99_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t99_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('22',plain,(
    ! [X37: $i] :
      ( ( m1_pre_topc @ X37 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ~ ( m1_pre_topc @ X38 @ X40 )
      | ( r1_tarski @ ( u1_struct_0 @ X38 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( m1_pre_topc @ X40 @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
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

thf('34',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_partfun1 @ X27 @ X28 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( r1_tarski @ ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 ) @ X30 )
      | ~ ( r1_tarski @ X29 @ X27 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t178_funct_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ( ( k2_partfun1 @ X23 @ X24 @ X22 @ X25 )
        = ( k7_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['35','38','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','47'])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 )
        = ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('53',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_E ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( ( k2_tmap_1 @ X35 @ X33 @ X36 @ X34 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) @ X36 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('57',plain,(
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
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62','63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ( k9_relat_1 @ sk_D @ sk_E )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) ),
    inference(demod,[status(thm)],['53','70'])).

thf('72',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_E ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','71'])).

thf('73',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['9','10'])).

thf('75',plain,
    ( ( ( k9_relat_1 @ sk_D @ sk_E )
     != ( k9_relat_1 @ sk_D @ sk_E ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['75'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('77',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('80',plain,(
    ! [X31: $i] :
      ( ( l1_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HpHdgSewOk
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.70  % Solved by: fo/fo7.sh
% 0.50/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.70  % done 269 iterations in 0.269s
% 0.50/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.70  % SZS output start Refutation
% 0.50/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.50/0.70  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.50/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.70  thf(sk_E_type, type, sk_E: $i).
% 0.50/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.50/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.50/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.50/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.50/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.70  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.50/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.50/0.70  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.50/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.70  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.50/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.50/0.70  thf(t61_tmap_1, conjecture,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.70       ( ![B:$i]:
% 0.50/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.50/0.70             ( l1_pre_topc @ B ) ) =>
% 0.50/0.70           ( ![C:$i]:
% 0.50/0.70             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.50/0.70               ( ![D:$i]:
% 0.50/0.70                 ( ( ( v1_funct_1 @ D ) & 
% 0.50/0.70                     ( v1_funct_2 @
% 0.50/0.70                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.50/0.70                     ( m1_subset_1 @
% 0.50/0.70                       D @ 
% 0.50/0.70                       ( k1_zfmisc_1 @
% 0.50/0.70                         ( k2_zfmisc_1 @
% 0.50/0.70                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.50/0.70                   ( ![E:$i]:
% 0.50/0.70                     ( ( m1_subset_1 @
% 0.50/0.70                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.50/0.70                       ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.50/0.70                         ( ( k7_relset_1 @
% 0.50/0.70                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) =
% 0.50/0.70                           ( k7_relset_1 @
% 0.50/0.70                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.50/0.70                             ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.70    (~( ![A:$i]:
% 0.50/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.50/0.70            ( l1_pre_topc @ A ) ) =>
% 0.50/0.70          ( ![B:$i]:
% 0.50/0.70            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.50/0.70                ( l1_pre_topc @ B ) ) =>
% 0.50/0.70              ( ![C:$i]:
% 0.50/0.70                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.50/0.70                  ( ![D:$i]:
% 0.50/0.70                    ( ( ( v1_funct_1 @ D ) & 
% 0.50/0.70                        ( v1_funct_2 @
% 0.50/0.70                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.50/0.70                        ( m1_subset_1 @
% 0.50/0.70                          D @ 
% 0.50/0.70                          ( k1_zfmisc_1 @
% 0.50/0.70                            ( k2_zfmisc_1 @
% 0.50/0.70                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.50/0.70                      ( ![E:$i]:
% 0.50/0.70                        ( ( m1_subset_1 @
% 0.50/0.70                            E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.50/0.70                          ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.50/0.70                            ( ( k7_relset_1 @
% 0.50/0.70                                ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.50/0.70                                D @ E ) =
% 0.50/0.70                              ( k7_relset_1 @
% 0.50/0.70                                ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.50/0.70                                ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.50/0.70    inference('cnf.neg', [status(esa)], [t61_tmap_1])).
% 0.50/0.70  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('1', plain, ((r1_tarski @ sk_E @ (u1_struct_0 @ sk_C))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(t162_relat_1, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( v1_relat_1 @ A ) =>
% 0.50/0.70       ( ![B:$i,C:$i]:
% 0.50/0.70         ( ( r1_tarski @ B @ C ) =>
% 0.50/0.70           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.50/0.70             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.50/0.70  thf('2', plain,
% 0.50/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.50/0.70         (~ (r1_tarski @ X7 @ X8)
% 0.50/0.70          | ((k9_relat_1 @ (k7_relat_1 @ X9 @ X8) @ X7)
% 0.50/0.70              = (k9_relat_1 @ X9 @ X7))
% 0.50/0.70          | ~ (v1_relat_1 @ X9))),
% 0.50/0.70      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.50/0.70  thf('3', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ X0)
% 0.50/0.70          | ((k9_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_E)
% 0.50/0.70              = (k9_relat_1 @ X0 @ sk_E)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.70  thf('4', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(cc2_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.50/0.70  thf('5', plain,
% 0.50/0.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.50/0.70         ((v5_relat_1 @ X15 @ X17)
% 0.50/0.70          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.50/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.50/0.70  thf('6', plain, ((v5_relat_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.50/0.70  thf(d19_relat_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( v1_relat_1 @ B ) =>
% 0.50/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.50/0.70  thf('7', plain,
% 0.50/0.70      (![X3 : $i, X4 : $i]:
% 0.50/0.70         (~ (v5_relat_1 @ X3 @ X4)
% 0.50/0.70          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.50/0.70          | ~ (v1_relat_1 @ X3))),
% 0.50/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.50/0.70  thf('8', plain,
% 0.50/0.70      ((~ (v1_relat_1 @ sk_D)
% 0.50/0.70        | (r1_tarski @ (k2_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.50/0.70  thf('9', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(cc1_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( v1_relat_1 @ C ) ))).
% 0.50/0.70  thf('10', plain,
% 0.50/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.50/0.70         ((v1_relat_1 @ X12)
% 0.50/0.70          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.50/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.70  thf('11', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.70  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['8', '11'])).
% 0.50/0.70  thf(t148_relat_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( v1_relat_1 @ B ) =>
% 0.50/0.70       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.50/0.70  thf('13', plain,
% 0.50/0.70      (![X5 : $i, X6 : $i]:
% 0.50/0.70         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.50/0.70          | ~ (v1_relat_1 @ X5))),
% 0.50/0.70      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.50/0.70  thf(t99_relat_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( v1_relat_1 @ B ) =>
% 0.50/0.70       ( r1_tarski @
% 0.50/0.70         ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k2_relat_1 @ B ) ) ))).
% 0.50/0.70  thf('14', plain,
% 0.50/0.70      (![X10 : $i, X11 : $i]:
% 0.50/0.70         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X10 @ X11)) @ 
% 0.50/0.70           (k2_relat_1 @ X10))
% 0.50/0.70          | ~ (v1_relat_1 @ X10))),
% 0.50/0.70      inference('cnf', [status(esa)], [t99_relat_1])).
% 0.50/0.70  thf('15', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.50/0.70          | ~ (v1_relat_1 @ X1)
% 0.50/0.70          | ~ (v1_relat_1 @ X1))),
% 0.50/0.70      inference('sup+', [status(thm)], ['13', '14'])).
% 0.50/0.70  thf('16', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ X1)
% 0.50/0.70          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.50/0.70      inference('simplify', [status(thm)], ['15'])).
% 0.50/0.70  thf(t1_xboole_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.50/0.70       ( r1_tarski @ A @ C ) ))).
% 0.50/0.70  thf('17', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (~ (r1_tarski @ X0 @ X1)
% 0.50/0.70          | ~ (r1_tarski @ X1 @ X2)
% 0.50/0.70          | (r1_tarski @ X0 @ X2))),
% 0.50/0.70      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.50/0.70  thf('18', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ X0)
% 0.50/0.70          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ X2)
% 0.50/0.70          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X2))),
% 0.50/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.50/0.70  thf('19', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (u1_struct_0 @ sk_A))
% 0.50/0.70          | ~ (v1_relat_1 @ sk_D))),
% 0.50/0.70      inference('sup-', [status(thm)], ['12', '18'])).
% 0.50/0.70  thf('20', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.70  thf('21', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.50/0.70  thf(t2_tsep_1, axiom,
% 0.50/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.50/0.70  thf('22', plain,
% 0.50/0.70      (![X37 : $i]: ((m1_pre_topc @ X37 @ X37) | ~ (l1_pre_topc @ X37))),
% 0.50/0.70      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.50/0.70  thf('23', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(t4_tsep_1, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.70       ( ![B:$i]:
% 0.50/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.50/0.70           ( ![C:$i]:
% 0.50/0.70             ( ( m1_pre_topc @ C @ A ) =>
% 0.50/0.70               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.50/0.70                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.50/0.70  thf('24', plain,
% 0.50/0.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.50/0.70         (~ (m1_pre_topc @ X38 @ X39)
% 0.50/0.70          | ~ (m1_pre_topc @ X38 @ X40)
% 0.50/0.70          | (r1_tarski @ (u1_struct_0 @ X38) @ (u1_struct_0 @ X40))
% 0.50/0.70          | ~ (m1_pre_topc @ X40 @ X39)
% 0.50/0.70          | ~ (l1_pre_topc @ X39)
% 0.50/0.70          | ~ (v2_pre_topc @ X39))),
% 0.50/0.70      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.50/0.70  thf('25', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (v2_pre_topc @ sk_B)
% 0.50/0.70          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.70          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.50/0.70          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.50/0.70          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.70  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('28', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.50/0.70          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.50/0.70          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.50/0.70      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.50/0.70  thf('29', plain,
% 0.50/0.70      ((~ (l1_pre_topc @ sk_B)
% 0.50/0.70        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.50/0.70        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['22', '28'])).
% 0.50/0.70  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('31', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('32', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.50/0.70      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.50/0.70  thf('33', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(t178_funct_2, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.50/0.70       ( ![E:$i]:
% 0.50/0.70         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.50/0.70             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.50/0.70           ( ( ( r1_tarski @ B @ A ) & 
% 0.50/0.70               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.50/0.70             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.50/0.70               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.50/0.70               ( m1_subset_1 @
% 0.50/0.70                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.50/0.70                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.50/0.70  thf('34', plain,
% 0.50/0.70      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.50/0.70         (~ (v1_funct_1 @ X26)
% 0.50/0.70          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.50/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.50/0.70          | (m1_subset_1 @ (k2_partfun1 @ X27 @ X28 @ X26 @ X29) @ 
% 0.50/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.50/0.70          | ~ (r1_tarski @ (k7_relset_1 @ X27 @ X28 @ X26 @ X29) @ X30)
% 0.50/0.70          | ~ (r1_tarski @ X29 @ X27)
% 0.50/0.70          | (v1_xboole_0 @ X28))),
% 0.50/0.70      inference('cnf', [status(esa)], [t178_funct_2])).
% 0.50/0.70  thf('35', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.50/0.70          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B))
% 0.50/0.70          | ~ (r1_tarski @ 
% 0.50/0.70               (k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70                sk_D @ X0) @ 
% 0.50/0.70               X1)
% 0.50/0.70          | (m1_subset_1 @ 
% 0.50/0.70             (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70              sk_D @ X0) @ 
% 0.50/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.50/0.70          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.50/0.70          | ~ (v1_funct_1 @ sk_D))),
% 0.50/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.50/0.70  thf('36', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(redefinition_k7_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.50/0.70  thf('37', plain,
% 0.50/0.70      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.50/0.70          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.50/0.70  thf('38', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.50/0.70           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.70  thf('39', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(redefinition_k2_partfun1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( ( v1_funct_1 @ C ) & 
% 0.50/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.70       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.50/0.70  thf('40', plain,
% 0.50/0.70      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.50/0.70          | ~ (v1_funct_1 @ X22)
% 0.50/0.70          | ((k2_partfun1 @ X23 @ X24 @ X22 @ X25) = (k7_relat_1 @ X22 @ X25)))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.50/0.70  thf('41', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.50/0.70            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.50/0.70          | ~ (v1_funct_1 @ sk_D))),
% 0.50/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.50/0.70  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('43', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.50/0.70           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.50/0.70      inference('demod', [status(thm)], ['41', '42'])).
% 0.50/0.70  thf('44', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('46', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.50/0.70          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B))
% 0.50/0.70          | ~ (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ X1)
% 0.50/0.70          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.50/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.50/0.70      inference('demod', [status(thm)], ['35', '38', '43', '44', '45'])).
% 0.50/0.70  thf('47', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.50/0.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ X0)))
% 0.50/0.70          | ~ (r1_tarski @ (k9_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)
% 0.50/0.70          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['32', '46'])).
% 0.50/0.70  thf('48', plain,
% 0.50/0.70      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.50/0.70        | (m1_subset_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ 
% 0.50/0.70           (k1_zfmisc_1 @ 
% 0.50/0.70            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['21', '47'])).
% 0.50/0.70  thf('49', plain,
% 0.50/0.70      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.50/0.70          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.50/0.70  thf('50', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.50/0.70          | ((k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70              (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)
% 0.50/0.70              = (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.50/0.70  thf('51', plain,
% 0.50/0.70      (((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.50/0.70         sk_E)
% 0.50/0.70         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('52', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k7_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.50/0.70           X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.70  thf('53', plain,
% 0.50/0.70      (((k9_relat_1 @ sk_D @ sk_E)
% 0.50/0.70         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70             (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_E))),
% 0.50/0.70      inference('demod', [status(thm)], ['51', '52'])).
% 0.50/0.70  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('55', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D @ 
% 0.50/0.70        (k1_zfmisc_1 @ 
% 0.50/0.70         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(d4_tmap_1, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.70       ( ![B:$i]:
% 0.50/0.70         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.50/0.70             ( l1_pre_topc @ B ) ) =>
% 0.50/0.70           ( ![C:$i]:
% 0.50/0.70             ( ( ( v1_funct_1 @ C ) & 
% 0.50/0.70                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.50/0.70                 ( m1_subset_1 @
% 0.50/0.70                   C @ 
% 0.50/0.70                   ( k1_zfmisc_1 @
% 0.50/0.70                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.50/0.70               ( ![D:$i]:
% 0.50/0.70                 ( ( m1_pre_topc @ D @ A ) =>
% 0.50/0.70                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.50/0.70                     ( k2_partfun1 @
% 0.50/0.70                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.50/0.70                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.70  thf('56', plain,
% 0.50/0.70      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.50/0.70         ((v2_struct_0 @ X33)
% 0.50/0.70          | ~ (v2_pre_topc @ X33)
% 0.50/0.70          | ~ (l1_pre_topc @ X33)
% 0.50/0.70          | ~ (m1_pre_topc @ X34 @ X35)
% 0.50/0.70          | ((k2_tmap_1 @ X35 @ X33 @ X36 @ X34)
% 0.50/0.70              = (k2_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ 
% 0.50/0.70                 X36 @ (u1_struct_0 @ X34)))
% 0.50/0.70          | ~ (m1_subset_1 @ X36 @ 
% 0.50/0.70               (k1_zfmisc_1 @ 
% 0.50/0.70                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 0.50/0.70          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 0.50/0.70          | ~ (v1_funct_1 @ X36)
% 0.50/0.70          | ~ (l1_pre_topc @ X35)
% 0.50/0.70          | ~ (v2_pre_topc @ X35)
% 0.50/0.70          | (v2_struct_0 @ X35))),
% 0.50/0.70      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.50/0.70  thf('57', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_struct_0 @ sk_B)
% 0.50/0.70          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.70          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.70          | ~ (v1_funct_1 @ sk_D)
% 0.50/0.70          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.50/0.70          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.50/0.70              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70                 sk_D @ (u1_struct_0 @ X0)))
% 0.50/0.70          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.50/0.70          | ~ (l1_pre_topc @ sk_A)
% 0.50/0.70          | ~ (v2_pre_topc @ sk_A)
% 0.50/0.70          | (v2_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.50/0.70  thf('58', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('61', plain,
% 0.50/0.70      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('62', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.50/0.70           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.50/0.70      inference('demod', [status(thm)], ['41', '42'])).
% 0.50/0.70  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('65', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((v2_struct_0 @ sk_B)
% 0.50/0.70          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.50/0.70              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.50/0.70          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.50/0.70          | (v2_struct_0 @ sk_A))),
% 0.50/0.70      inference('demod', [status(thm)],
% 0.50/0.70                ['57', '58', '59', '60', '61', '62', '63', '64'])).
% 0.50/0.70  thf('66', plain,
% 0.50/0.70      (((v2_struct_0 @ sk_A)
% 0.50/0.70        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.50/0.70            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.50/0.70        | (v2_struct_0 @ sk_B))),
% 0.50/0.70      inference('sup-', [status(thm)], ['54', '65'])).
% 0.50/0.70  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('68', plain,
% 0.50/0.70      (((v2_struct_0 @ sk_B)
% 0.50/0.70        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.50/0.70            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.50/0.70      inference('clc', [status(thm)], ['66', '67'])).
% 0.50/0.70  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('70', plain,
% 0.50/0.70      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.50/0.70         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.50/0.70      inference('clc', [status(thm)], ['68', '69'])).
% 0.50/0.70  thf('71', plain,
% 0.50/0.70      (((k9_relat_1 @ sk_D @ sk_E)
% 0.50/0.70         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.70             (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))),
% 0.50/0.70      inference('demod', [status(thm)], ['53', '70'])).
% 0.50/0.70  thf('72', plain,
% 0.50/0.70      ((((k9_relat_1 @ sk_D @ sk_E)
% 0.50/0.70          != (k9_relat_1 @ (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) @ sk_E))
% 0.50/0.70        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['50', '71'])).
% 0.50/0.70  thf('73', plain,
% 0.50/0.70      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.50/0.70        | ~ (v1_relat_1 @ sk_D)
% 0.50/0.70        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['3', '72'])).
% 0.50/0.70  thf('74', plain, ((v1_relat_1 @ sk_D)),
% 0.50/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.70  thf('75', plain,
% 0.50/0.70      ((((k9_relat_1 @ sk_D @ sk_E) != (k9_relat_1 @ sk_D @ sk_E))
% 0.50/0.70        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.70      inference('demod', [status(thm)], ['73', '74'])).
% 0.50/0.70  thf('76', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.50/0.70      inference('simplify', [status(thm)], ['75'])).
% 0.50/0.70  thf(fc2_struct_0, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.50/0.70       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.50/0.70  thf('77', plain,
% 0.50/0.70      (![X32 : $i]:
% 0.50/0.70         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.50/0.70          | ~ (l1_struct_0 @ X32)
% 0.50/0.70          | (v2_struct_0 @ X32))),
% 0.50/0.70      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.50/0.70  thf('78', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['76', '77'])).
% 0.50/0.70  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(dt_l1_pre_topc, axiom,
% 0.50/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.50/0.70  thf('80', plain,
% 0.50/0.70      (![X31 : $i]: ((l1_struct_0 @ X31) | ~ (l1_pre_topc @ X31))),
% 0.50/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.70  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.50/0.70      inference('sup-', [status(thm)], ['79', '80'])).
% 0.50/0.70  thf('82', plain, ((v2_struct_0 @ sk_A)),
% 0.50/0.70      inference('demod', [status(thm)], ['78', '81'])).
% 0.50/0.70  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.50/0.70  
% 0.50/0.70  % SZS output end Refutation
% 0.50/0.70  
% 0.50/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
