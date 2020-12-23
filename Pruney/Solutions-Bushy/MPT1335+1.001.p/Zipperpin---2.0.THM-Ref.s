%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1335+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dgZHHy1T9z

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:30 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 561 expanded)
%              Number of leaves         :   34 ( 173 expanded)
%              Depth                    :   21
%              Number of atoms          : 1915 (18769 expanded)
%              Number of equality atoms :   18 (  74 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t58_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( v5_pre_topc @ D @ A @ C )
                          & ( v5_pre_topc @ E @ C @ B ) )
                       => ( v5_pre_topc @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ E ) @ A @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( l1_pre_topc @ C ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( ( v5_pre_topc @ D @ A @ C )
                            & ( v5_pre_topc @ E @ C @ B ) )
                         => ( v5_pre_topc @ ( k1_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ D @ E ) @ A @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_tops_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X38 @ X37 ) @ X39 )
        = ( k10_relat_1 @ X38 @ ( k10_relat_1 @ X37 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ B @ C )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ( ( v1_funct_1 @ ( k5_relat_1 @ D @ E ) )
        & ( v1_funct_2 @ ( k5_relat_1 @ D @ E ) @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X26 ) ) )
      | ( v1_funct_2 @ ( k5_relat_1 @ X22 @ X25 ) @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ X1 ) @ ( u1_struct_0 @ sk_A_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ X1 ) @ ( u1_struct_0 @ sk_A_2 ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X10 @ X11 @ X13 @ X14 @ X9 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ X2 @ X0 @ sk_D_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ X2 @ X0 @ sk_D_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 )
        = ( k5_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ X2 @ X1 @ sk_D_1 @ X0 )
        = ( k5_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ X2 @ X1 @ sk_D_1 @ X0 )
        = ( k5_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E )
      = ( k5_relat_1 @ sk_D_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E )
    = ( k5_relat_1 @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20','29'])).

thf(d12_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_pre_topc @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( v4_pre_topc @ D @ B )
                     => ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ A ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A_2 )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X10 @ X11 @ X13 @ X14 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ X2 @ X1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ X2 @ X1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E )
    = ( k5_relat_1 @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('44',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['32','33','44','45'])).

thf('47',plain,(
    ~ ( v5_pre_topc @ ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_partfun1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_D_1 @ sk_E )
    = ( k5_relat_1 @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('49',plain,(
    ~ ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 ) @ sk_C )
      | ~ ( v4_pre_topc @ X0 @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_E @ sk_C @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v5_pre_topc @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 ) @ sk_C )
      | ~ ( v4_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('62',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k8_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k10_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_E @ X0 ) @ sk_C )
      | ~ ( v4_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ sk_B_1 )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_E @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['51','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('67',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20','29'])).

thf('68',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v4_pre_topc @ ( sk_D @ X6 @ X5 @ X7 ) @ X5 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A_2 )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('72',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 )
    | ( v4_pre_topc @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ~ ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('75',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ sk_B_1 )
    | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v4_pre_topc @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,
    ( ( v4_pre_topc @ ( k10_relat_1 @ sk_E @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) ) @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['65','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k8_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('79',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( m1_subset_1 @ ( k8_relset_1 @ X16 @ X17 @ X15 @ X18 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 )
      = ( k10_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k10_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( v4_pre_topc @ X8 @ X5 )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A_2 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 ) @ sk_A_2 )
      | ~ ( v4_pre_topc @ X0 @ sk_C )
      | ~ ( v5_pre_topc @ sk_D_1 @ sk_A_2 @ sk_C )
      | ~ ( l1_pre_topc @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_D_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v5_pre_topc @ sk_D_1 @ sk_A_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 ) @ sk_A_2 )
      | ~ ( v4_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k8_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k10_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) @ sk_D_1 @ X0 )
      = ( k10_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_D_1 @ X0 ) @ sk_A_2 )
      | ~ ( v4_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k10_relat_1 @ sk_E @ X0 ) @ sk_C )
      | ( v4_pre_topc @ ( k10_relat_1 @ sk_D_1 @ ( k10_relat_1 @ sk_E @ X0 ) ) @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['82','95'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v4_pre_topc @ ( k10_relat_1 @ sk_D_1 @ ( k10_relat_1 @ sk_E @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) ) ) @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['77','96'])).

thf('98',plain,
    ( ( v4_pre_topc @ ( k10_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) ) @ sk_A_2 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('100',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('101',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('104',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v4_pre_topc @ ( k10_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) ) @ sk_A_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','101','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20','29'])).

thf('107',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k8_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k10_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ X0 )
      = ( k10_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v4_pre_topc @ ( k8_relset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) @ X6 @ ( sk_D @ X6 @ X5 @ X7 ) ) @ X7 )
      | ( v5_pre_topc @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( v1_funct_2 @ X6 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d12_pre_topc])).

thf('110',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) ) @ sk_A_2 )
    | ~ ( l1_pre_topc @ sk_A_2 )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) )
    | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_A_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('113',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','20','29'])).

thf('114',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( v4_pre_topc @ ( k10_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) ) @ sk_A_2 )
    | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    ~ ( v5_pre_topc @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_A_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('117',plain,
    ( ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v4_pre_topc @ ( k10_relat_1 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( sk_D @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ sk_B_1 @ sk_A_2 ) ) @ sk_A_2 ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['105','117'])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( v1_funct_2 @ ( k5_relat_1 @ sk_D_1 @ sk_E ) @ ( u1_struct_0 @ sk_A_2 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('120',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['118','119'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('121',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('124',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('125',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_struct_0 @ sk_C ),
    inference(demod,[status(thm)],['122','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['0','126'])).


%------------------------------------------------------------------------------
