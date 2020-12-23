%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OfNcfJlKEQ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 148 expanded)
%              Number of leaves         :   34 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  897 (4147 expanded)
%              Number of equality atoms :   30 (  80 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X6 @ X5 ) @ X4 )
        = ( k1_funct_1 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
        = ( k1_funct_1 @ X0 @ sk_F ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ X15 )
      | ( ( k3_funct_2 @ X15 @ X16 @ X14 @ X17 )
        = ( k1_funct_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['10','25'])).

thf('27',plain,
    ( ( k3_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
    = ( k1_funct_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    ( k1_funct_1 @ sk_E @ sk_F )
 != ( k1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(demod,[status(thm)],['3','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
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

thf('32',plain,(
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

thf('33',plain,(
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
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 )
        = ( k7_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
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
    inference(demod,[status(thm)],['33','34','35','40','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ( k1_funct_1 @ sk_E @ sk_F )
 != ( k1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F ) ),
    inference(demod,[status(thm)],['28','54'])).

thf('56',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_F )
     != ( k1_funct_1 @ sk_E @ sk_F ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('58',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ( k1_funct_1 @ sk_E @ sk_F )
 != ( k1_funct_1 @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['56','59','60'])).

thf('62',plain,(
    $false ),
    inference(simplify,[status(thm)],['61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OfNcfJlKEQ
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 47 iterations in 0.014s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(t72_tmap_1, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48             ( l1_pre_topc @ B ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.48                   ( ![E:$i]:
% 0.19/0.48                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.48                         ( v1_funct_2 @
% 0.19/0.48                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.48                         ( m1_subset_1 @
% 0.19/0.48                           E @ 
% 0.19/0.48                           ( k1_zfmisc_1 @
% 0.19/0.48                             ( k2_zfmisc_1 @
% 0.19/0.48                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.48                       ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.48                         ( ![F:$i]:
% 0.19/0.48                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.48                             ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.48                               ( ( k3_funct_2 @
% 0.19/0.48                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.19/0.48                                   E @ F ) =
% 0.19/0.48                                 ( k1_funct_1 @
% 0.19/0.48                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.48            ( l1_pre_topc @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48                ( l1_pre_topc @ B ) ) =>
% 0.19/0.48              ( ![C:$i]:
% 0.19/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.48                  ( ![D:$i]:
% 0.19/0.48                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.48                      ( ![E:$i]:
% 0.19/0.48                        ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.48                            ( v1_funct_2 @
% 0.19/0.48                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.48                            ( m1_subset_1 @
% 0.19/0.48                              E @ 
% 0.19/0.48                              ( k1_zfmisc_1 @
% 0.19/0.48                                ( k2_zfmisc_1 @
% 0.19/0.48                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.48                          ( ( m1_pre_topc @ C @ D ) =>
% 0.19/0.48                            ( ![F:$i]:
% 0.19/0.48                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.48                                ( ( r2_hidden @ F @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.48                                  ( ( k3_funct_2 @
% 0.19/0.48                                      ( u1_struct_0 @ D ) @ 
% 0.19/0.48                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.19/0.48                                    ( k1_funct_1 @
% 0.19/0.48                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t72_tmap_1])).
% 0.19/0.48  thf('0', plain, ((r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t72_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48       ( ( r2_hidden @ A @ B ) =>
% 0.19/0.48         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X4 @ X5)
% 0.19/0.48          | ~ (v1_relat_1 @ X6)
% 0.19/0.48          | ~ (v1_funct_1 @ X6)
% 0.19/0.48          | ((k1_funct_1 @ (k7_relat_1 @ X6 @ X5) @ X4)
% 0.19/0.48              = (k1_funct_1 @ X6 @ X4)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_funct_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ sk_F)
% 0.19/0.48            = (k1_funct_1 @ X0 @ sk_F))
% 0.19/0.48          | ~ (v1_funct_1 @ X0)
% 0.19/0.48          | ~ (v1_relat_1 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_F)
% 0.19/0.48         != (k1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('4', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k3_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.48         ( m1_subset_1 @ D @ A ) ) =>
% 0.19/0.48       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.19/0.48          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.19/0.48          | ~ (v1_funct_1 @ X14)
% 0.19/0.48          | (v1_xboole_0 @ X15)
% 0.19/0.48          | ~ (m1_subset_1 @ X17 @ X15)
% 0.19/0.48          | ((k3_funct_2 @ X15 @ X16 @ X14 @ X17) = (k1_funct_1 @ X14 @ X17)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.48            X0) = (k1_funct_1 @ sk_E @ X0))
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.19/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.19/0.48          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.48          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.48            X0) = (k1_funct_1 @ sk_E @ X0))
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.19/0.48          | (v1_xboole_0 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.48  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t1_tsep_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.48           ( m1_subset_1 @
% 0.19/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X25 : $i, X26 : $i]:
% 0.19/0.48         (~ (m1_pre_topc @ X25 @ X26)
% 0.19/0.48          | (m1_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.19/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.19/0.48          | ~ (l1_pre_topc @ X26))),
% 0.19/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((~ (l1_pre_topc @ sk_D)
% 0.19/0.48        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(dt_m1_pre_topc, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( l1_pre_topc @ A ) =>
% 0.19/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i]:
% 0.19/0.48         (~ (m1_pre_topc @ X18 @ X19)
% 0.19/0.48          | (l1_pre_topc @ X18)
% 0.19/0.48          | ~ (l1_pre_topc @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.48  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.48  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('18', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '18'])).
% 0.19/0.48  thf(cc1_subset_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.19/0.48          | (v1_xboole_0 @ X2)
% 0.19/0.48          | ~ (v1_xboole_0 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.19/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain, ((r2_hidden @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t7_boole, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_boole])).
% 0.19/0.48  thf('24', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_D))),
% 0.19/0.48      inference('clc', [status(thm)], ['21', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.19/0.48          | ((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.48              sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.19/0.48      inference('clc', [status(thm)], ['10', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (((k3_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_F)
% 0.19/0.48         = (k1_funct_1 @ sk_E @ sk_F))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (((k1_funct_1 @ sk_E @ sk_F)
% 0.19/0.48         != (k1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '27'])).
% 0.19/0.48  thf('29', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d5_tmap_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.48             ( l1_pre_topc @ B ) ) =>
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.48               ( ![D:$i]:
% 0.19/0.48                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.48                   ( ![E:$i]:
% 0.19/0.48                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.48                         ( v1_funct_2 @
% 0.19/0.48                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.48                         ( m1_subset_1 @
% 0.19/0.48                           E @ 
% 0.19/0.48                           ( k1_zfmisc_1 @
% 0.19/0.48                             ( k2_zfmisc_1 @
% 0.19/0.48                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.48                       ( ( m1_pre_topc @ D @ C ) =>
% 0.19/0.48                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.48                           ( k2_partfun1 @
% 0.19/0.48                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.19/0.48                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X20)
% 0.19/0.48          | ~ (v2_pre_topc @ X20)
% 0.19/0.48          | ~ (l1_pre_topc @ X20)
% 0.19/0.48          | ~ (m1_pre_topc @ X21 @ X22)
% 0.19/0.48          | ~ (m1_pre_topc @ X21 @ X23)
% 0.19/0.48          | ((k3_tmap_1 @ X22 @ X20 @ X23 @ X21 @ X24)
% 0.19/0.48              = (k2_partfun1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20) @ 
% 0.19/0.48                 X24 @ (u1_struct_0 @ X21)))
% 0.19/0.48          | ~ (m1_subset_1 @ X24 @ 
% 0.19/0.48               (k1_zfmisc_1 @ 
% 0.19/0.48                (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20))))
% 0.19/0.48          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X20))
% 0.19/0.48          | ~ (v1_funct_1 @ X24)
% 0.19/0.48          | ~ (m1_pre_topc @ X23 @ X22)
% 0.19/0.48          | ~ (l1_pre_topc @ X22)
% 0.19/0.48          | ~ (v2_pre_topc @ X22)
% 0.19/0.48          | (v2_struct_0 @ X22))),
% 0.19/0.48      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((v2_struct_0 @ X0)
% 0.19/0.48          | ~ (v2_pre_topc @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ X0)
% 0.19/0.48          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.48          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.19/0.48          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.19/0.48              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.19/0.48                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.48          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.48          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.48          | (v2_struct_0 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_E @ 
% 0.19/0.48        (k1_zfmisc_1 @ 
% 0.19/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k2_partfun1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.49       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.19/0.49          | ~ (v1_funct_1 @ X10)
% 0.19/0.49          | ((k2_partfun1 @ X11 @ X12 @ X10 @ X13) = (k7_relat_1 @ X10 @ X13)))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.49            X0) = (k7_relat_1 @ sk_E @ X0))
% 0.19/0.49          | ~ (v1_funct_1 @ sk_E))),
% 0.19/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf('39', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.19/0.49           X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('42', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v2_pre_topc @ X0)
% 0.19/0.49          | ~ (l1_pre_topc @ X0)
% 0.19/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.49          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.19/0.49              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['33', '34', '35', '40', '41', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_B)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.19/0.49              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['30', '43'])).
% 0.19/0.49  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_B)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.19/0.49              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.19/0.49            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.49        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.49        | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['29', '47'])).
% 0.19/0.49  thf('49', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.19/0.49            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.49        | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['48', '49'])).
% 0.19/0.49  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B)
% 0.19/0.49        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.19/0.49            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 0.19/0.49      inference('clc', [status(thm)], ['50', '51'])).
% 0.19/0.49  thf('53', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.19/0.49         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('clc', [status(thm)], ['52', '53'])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (((k1_funct_1 @ sk_E @ sk_F)
% 0.19/0.49         != (k1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))),
% 0.19/0.49      inference('demod', [status(thm)], ['28', '54'])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      ((((k1_funct_1 @ sk_E @ sk_F) != (k1_funct_1 @ sk_E @ sk_F))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_E)
% 0.19/0.49        | ~ (v1_funct_1 @ sk_E))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '55'])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc1_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( v1_relat_1 @ C ) ))).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.49         ((v1_relat_1 @ X7)
% 0.19/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.49  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 0.19/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.49  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('61', plain,
% 0.19/0.49      (((k1_funct_1 @ sk_E @ sk_F) != (k1_funct_1 @ sk_E @ sk_F))),
% 0.19/0.49      inference('demod', [status(thm)], ['56', '59', '60'])).
% 0.19/0.49  thf('62', plain, ($false), inference('simplify', [status(thm)], ['61'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
