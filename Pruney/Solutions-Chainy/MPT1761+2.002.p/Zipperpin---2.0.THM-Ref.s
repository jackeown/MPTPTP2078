%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EybGWPGZZe

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 156 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  941 (4451 expanded)
%              Number of equality atoms :   30 (  84 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X10 @ X9 ) @ X8 )
        = ( k1_funct_1 @ X10 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
        = ( k1_funct_1 @ X0 @ sk_F ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_F )
 != ( k1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ X19 )
      | ( ( k3_funct_2 @ X19 @ X20 @ X18 @ X21 )
        = ( k1_funct_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
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

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X29 )
      | ( r1_tarski @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X29 @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','28'])).

thf('30',plain,
    ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ sk_F )
    = ( k1_funct_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf('31',plain,(
    ( k1_funct_1 @ sk_E @ sk_F )
 != ( k1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','30'])).

thf('32',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
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

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X25 )
      | ( ( k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) @ X26 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X26 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_partfun1 @ X15 @ X16 @ X14 @ X17 )
        = ( k7_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37','38','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ( k1_funct_1 @ sk_E @ sk_F )
 != ( k1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['31','57'])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_F )
     != ( k1_funct_1 @ sk_E @ sk_F ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ( k1_funct_1 @ sk_E @ sk_F )
 != ( k1_funct_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['59','62','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EybGWPGZZe
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 53 iterations in 0.028s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(t72_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                         ( v1_funct_2 @
% 0.21/0.49                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                         ( m1_subset_1 @
% 0.21/0.49                           E @ 
% 0.21/0.49                           ( k1_zfmisc_1 @
% 0.21/0.49                             ( k2_zfmisc_1 @
% 0.21/0.49                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                       ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.49                         ( ![F:$i]:
% 0.21/0.49                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.49                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                               ( ( k3_funct_2 @
% 0.21/0.49                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.21/0.49                                   E @ F ) =
% 0.21/0.49                                 ( k1_funct_1 @
% 0.21/0.49                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49                ( l1_pre_topc @ B ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.49                      ( ![E:$i]:
% 0.21/0.49                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                            ( v1_funct_2 @
% 0.21/0.49                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                            ( m1_subset_1 @
% 0.21/0.49                              E @ 
% 0.21/0.49                              ( k1_zfmisc_1 @
% 0.21/0.49                                ( k2_zfmisc_1 @
% 0.21/0.49                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                          ( ( m1_pre_topc @ C @ D ) =>
% 0.21/0.49                            ( ![F:$i]:
% 0.21/0.49                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.49                                ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                                  ( ( k3_funct_2 @
% 0.21/0.49                                      ( u1_struct_0 @ D ) @ 
% 0.21/0.49                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.21/0.49                                    ( k1_funct_1 @
% 0.21/0.49                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t72_tmap_1])).
% 0.21/0.49  thf('0', plain, ((r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t72_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.49          | ~ (v1_relat_1 @ X10)
% 0.21/0.49          | ~ (v1_funct_1 @ X10)
% 0.21/0.49          | ((k1_funct_1 @ (k7_relat_1 @ X10 @ X9) @ X8)
% 0.21/0.49              = (k1_funct_1 @ X10 @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 0.21/0.49            = (k1_funct_1 @ X0 @ sk_F))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ 
% 0.21/0.49         sk_F)
% 0.21/0.49         != (k1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.21/0.49             sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.49       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.49          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.21/0.49          | ~ (v1_funct_1 @ X18)
% 0.21/0.49          | (v1_xboole_0 @ X19)
% 0.21/0.49          | ~ (m1_subset_1 @ X21 @ X19)
% 0.21/0.49          | ((k3_funct_2 @ X19 @ X20 @ X18 @ X21) = (k1_funct_1 @ X18 @ X21)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49            sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.49               (u1_struct_0 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.49  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49            sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.49  thf('11', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t4_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.49               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.21/0.49                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X27 @ X28)
% 0.21/0.49          | ~ (m1_pre_topc @ X27 @ X29)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X29))
% 0.21/0.49          | ~ (m1_pre_topc @ X29 @ X28)
% 0.21/0.49          | ~ (l1_pre_topc @ X28)
% 0.21/0.49          | ~ (v2_pre_topc @ X28))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v2_pre_topc @ sk_A)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.49        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '17'])).
% 0.21/0.49  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X5 : $i, X7 : $i]:
% 0.21/0.49         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf(cc1_subset_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.49          | (v1_xboole_0 @ X3)
% 0.21/0.49          | ~ (v1_xboole_0 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.21/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain, ((r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf('27', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D))),
% 0.21/0.49      inference('clc', [status(thm)], ['24', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49              sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['10', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ sk_E @ 
% 0.21/0.49         sk_F) = (k1_funct_1 @ sk_E @ sk_F))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((k1_funct_1 @ sk_E @ sk_F)
% 0.21/0.49         != (k1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E) @ 
% 0.21/0.49             sk_F))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '30'])).
% 0.21/0.49  thf('32', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d5_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                         ( v1_funct_2 @
% 0.21/0.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                         ( m1_subset_1 @
% 0.21/0.49                           E @ 
% 0.21/0.49                           ( k1_zfmisc_1 @
% 0.21/0.49                             ( k2_zfmisc_1 @
% 0.21/0.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.49                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49                           ( k2_partfun1 @
% 0.21/0.49                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.21/0.49                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X22)
% 0.21/0.49          | ~ (v2_pre_topc @ X22)
% 0.21/0.49          | ~ (l1_pre_topc @ X22)
% 0.21/0.49          | ~ (m1_pre_topc @ X23 @ X24)
% 0.21/0.49          | ~ (m1_pre_topc @ X23 @ X25)
% 0.21/0.49          | ((k3_tmap_1 @ X24 @ X22 @ X25 @ X23 @ X26)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22) @ 
% 0.21/0.49                 X26 @ (u1_struct_0 @ X23)))
% 0.21/0.49          | ~ (m1_subset_1 @ X26 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))))
% 0.21/0.49          | ~ (v1_funct_2 @ X26 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X22))
% 0.21/0.49          | ~ (v1_funct_1 @ X26)
% 0.21/0.49          | ~ (m1_pre_topc @ X25 @ X24)
% 0.21/0.49          | ~ (l1_pre_topc @ X24)
% 0.21/0.49          | ~ (v2_pre_topc @ X24)
% 0.21/0.49          | (v2_struct_0 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ 
% 0.21/0.49               (u1_struct_0 @ sk_B_1))
% 0.21/0.49          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_B_1)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.21/0.49          | ~ (v1_funct_1 @ X14)
% 0.21/0.49          | ((k2_partfun1 @ X15 @ X16 @ X14 @ X17) = (k7_relat_1 @ X14 @ X17)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49            sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain, ((v2_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.49          | ((k3_tmap_1 @ X0 @ sk_B_1 @ sk_D @ X1 @ sk_E)
% 0.21/0.49              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['36', '37', '38', '43', '44', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_B_1)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ((k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.21/0.49              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '46'])).
% 0.21/0.49  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_B_1)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ((k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ X0 @ sk_E)
% 0.21/0.49              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E)
% 0.21/0.49            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.49        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '50'])).
% 0.21/0.49  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E)
% 0.21/0.49            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1)
% 0.21/0.49        | ((k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E)
% 0.21/0.49            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.21/0.49      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('56', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((k3_tmap_1 @ sk_A @ sk_B_1 @ sk_D @ sk_C @ sk_E)
% 0.21/0.49         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.21/0.49      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (((k1_funct_1 @ sk_E @ sk_F)
% 0.21/0.49         != (k1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_E @ sk_F) != (k1_funct_1 @ sk_E @ sk_F))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_E)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( v1_relat_1 @ C ) ))).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         ((v1_relat_1 @ X11)
% 0.21/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.49  thf('62', plain, ((v1_relat_1 @ sk_E)),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('63', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (((k1_funct_1 @ sk_E @ sk_F) != (k1_funct_1 @ sk_E @ sk_F))),
% 0.21/0.49      inference('demod', [status(thm)], ['59', '62', '63'])).
% 0.21/0.49  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
