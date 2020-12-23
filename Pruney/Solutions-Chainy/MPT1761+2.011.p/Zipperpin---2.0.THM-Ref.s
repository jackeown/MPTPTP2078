%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TR7BDUWjMi

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 148 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   18
%              Number of atoms          :  906 (4156 expanded)
%              Number of equality atoms :   29 (  79 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t72_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                = ( k1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) )
                               => ( ( k3_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                  = ( k1_funct_1 @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_tmap_1])).

thf('0',plain,(
    r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X9 @ X8 ) @ X7 )
        = ( k1_funct_1 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
        = ( k1_funct_1 @ X0 @ sk_F ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ X15 )
      | ( ( k3_funct_2 @ X15 @ X16 @ X14 @ X17 )
        = ( k1_funct_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
      = ( k1_funct_1 @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X23 )
      | ( ( k3_tmap_1 @ X22 @ X20 @ X23 @ X21 @ X24 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X20 ) @ X24 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X20 ) ) ) )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 )
        = ( k7_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['23','49'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_F )
     != ( k1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','50'])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_F )
     != ( k1_funct_1 @ sk_E @ sk_F ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('57',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_F )
     != ( k1_funct_1 @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['52','57','58'])).

thf('60',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','60'])).

thf('62',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TR7BDUWjMi
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 51 iterations in 0.027s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(t72_tmap_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48             ( l1_pre_topc @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.48                   ( ![E:$i]:
% 0.20/0.48                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.48                         ( v1_funct_2 @
% 0.20/0.48                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.48                         ( m1_subset_1 @
% 0.20/0.48                           E @ 
% 0.20/0.48                           ( k1_zfmisc_1 @
% 0.20/0.48                             ( k2_zfmisc_1 @
% 0.20/0.48                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.48                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.48                         ( ![F:$i]:
% 0.20/0.48                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.48                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.48                               ( ( k3_funct_2 @
% 0.20/0.48                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.48                                   E @ F ) =
% 0.20/0.48                                 ( k1_funct_1 @
% 0.20/0.48                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48                ( l1_pre_topc @ B ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.48                  ( ![D:$i]:
% 0.20/0.48                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.48                      ( ![E:$i]:
% 0.20/0.48                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.48                            ( v1_funct_2 @
% 0.20/0.48                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.48                            ( m1_subset_1 @
% 0.20/0.48                              E @ 
% 0.20/0.48                              ( k1_zfmisc_1 @
% 0.20/0.48                                ( k2_zfmisc_1 @
% 0.20/0.48                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.48                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.48                            ( ![F:$i]:
% 0.20/0.48                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.48                                ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.48                                  ( ( k3_funct_2 @
% 0.20/0.48                                      ( u1_struct_0 @ D ) @ 
% 0.20/0.48                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.20/0.48                                    ( k1_funct_1 @
% 0.20/0.48                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t72_tmap_1])).
% 0.20/0.48  thf('0', plain, ((r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t1_tsep_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( m1_subset_1 @
% 0.20/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X25 : $i, X26 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X25 @ X26)
% 0.20/0.48          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.20/0.48          | ~ (l1_pre_topc @ X26))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.48        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_m1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.48          | (l1_pre_topc @ X18)
% 0.20/0.48          | ~ (l1_pre_topc @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.48  thf('6', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '8'])).
% 0.20/0.48  thf(t5_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.48          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | ~ (v1_xboole_0 @ X2)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, ((r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t72_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.48         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.48          | ~ (v1_relat_1 @ X9)
% 0.20/0.48          | ~ (v1_funct_1 @ X9)
% 0.20/0.48          | ((k1_funct_1 @ (k7_relat_1 @ X9 @ X8) @ X7)
% 0.20/0.48              = (k1_funct_1 @ X9 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_funct_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 0.20/0.48            = (k1_funct_1 @ X0 @ sk_F))
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.48       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.48          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.20/0.48          | ~ (v1_funct_1 @ X14)
% 0.20/0.48          | (v1_xboole_0 @ X15)
% 0.20/0.48          | ~ (m1_subset_1 @ X17 @ X15)
% 0.20/0.48          | ((k3_funct_2 @ X15 @ X16 @ X14 @ X17) = (k1_funct_1 @ X14 @ X17)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.48            X0) = (k1_funct_1 @ sk_E @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.48          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.48          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.48            X0) = (k1_funct_1 @ sk_E @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.20/0.48        | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.48            sk_F) = (k1_funct_1 @ sk_E @ sk_F)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_F)
% 0.20/0.48         != (k1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d5_tmap_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.48             ( l1_pre_topc @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.48                   ( ![E:$i]:
% 0.20/0.48                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.48                         ( v1_funct_2 @
% 0.20/0.48                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.48                         ( m1_subset_1 @
% 0.20/0.48                           E @ 
% 0.20/0.48                           ( k1_zfmisc_1 @
% 0.20/0.48                             ( k2_zfmisc_1 @
% 0.20/0.48                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.48                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.48                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.48                           ( k2_partfun1 @
% 0.20/0.48                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.48                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X20)
% 0.20/0.48          | ~ (v2_pre_topc @ X20)
% 0.20/0.48          | ~ (l1_pre_topc @ X20)
% 0.20/0.48          | ~ (m1_pre_topc @ X21 @ X22)
% 0.20/0.48          | ~ (m1_pre_topc @ X21 @ X23)
% 0.20/0.48          | ((k3_tmap_1 @ X22 @ X20 @ X23 @ X21 @ X24)
% 0.20/0.48              = (k2_partfun1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20) @ 
% 0.20/0.48                 X24 @ (u1_struct_0 @ X21)))
% 0.20/0.48          | ~ (m1_subset_1 @ X24 @ 
% 0.20/0.48               (k1_zfmisc_1 @ 
% 0.20/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20))))
% 0.20/0.48          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20))
% 0.20/0.48          | ~ (v1_funct_1 @ X24)
% 0.20/0.48          | ~ (m1_pre_topc @ X23 @ X22)
% 0.20/0.48          | ~ (l1_pre_topc @ X22)
% 0.20/0.48          | ~ (v2_pre_topc @ X22)
% 0.20/0.48          | (v2_struct_0 @ X22))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.48          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.48              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.48          | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k2_partfun1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.20/0.48          | ~ (v1_funct_1 @ X10)
% 0.20/0.48          | ((k2_partfun1 @ X11 @ X12 @ X10 @ X13) = (k7_relat_1 @ X10 @ X13)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.48            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.48           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('37', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v2_struct_0 @ X0)
% 0.20/0.48          | ~ (v2_pre_topc @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.48              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.48          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.48          | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29', '30', '35', '36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.48          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.48              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '38'])).
% 0.20/0.48  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v2_struct_0 @ sk_B)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.48          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.48              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.48          | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.48            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.48        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '42'])).
% 0.20/0.48  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.48            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.48        | (v2_struct_0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_B)
% 0.20/0.48        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.48            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.48      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.48         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_F)
% 0.20/0.48         != (k1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((((k1_funct_1 @ sk_E @ sk_F)
% 0.20/0.48          != (k1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 0.20/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '50'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      ((((k1_funct_1 @ sk_E @ sk_F) != (k1_funct_1 @ sk_E @ sk_F))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_E)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_E @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.48          | (v1_relat_1 @ X3)
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ 
% 0.20/0.48           (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.48        | (v1_relat_1 @ sk_E))),
% 0.20/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf(fc6_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.48  thf('57', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.48      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain,
% 0.20/0.48      ((((k1_funct_1 @ sk_E @ sk_F) != (k1_funct_1 @ sk_E @ sk_F))
% 0.20/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['52', '57', '58'])).
% 0.20/0.48  thf('60', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_D))),
% 0.20/0.48      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.48  thf('61', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '60'])).
% 0.20/0.48  thf('62', plain, ($false), inference('sup-', [status(thm)], ['0', '61'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
