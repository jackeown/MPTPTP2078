%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MAkn7gkj30

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:09 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  383 (3632 expanded)
%              Number of leaves         :   46 (1027 expanded)
%              Depth                    :   29
%              Number of atoms          : 4624 (201484 expanded)
%              Number of equality atoms :   91 (2366 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t80_tmap_1,conjecture,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ! [G: $i] :
                              ( ( ( v1_funct_1 @ G )
                                & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                             => ( ( ( D = A )
                                  & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                               => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                               => ( ( ( D = A )
                                    & ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ G ) )
                                 => ( ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F )
                                  <=> ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t78_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( m1_pre_topc @ C @ D )
                       => ( r2_funct_2 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( v2_struct_0 @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ~ ( l1_pre_topc @ X45 )
      | ( v2_struct_0 @ X46 )
      | ~ ( m1_pre_topc @ X46 @ X47 )
      | ~ ( m1_pre_topc @ X48 @ X46 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X45 ) @ ( k3_tmap_1 @ X47 @ X45 @ X46 @ X48 @ ( k2_tmap_1 @ X47 @ X45 @ X49 @ X46 ) ) @ ( k2_tmap_1 @ X47 @ X45 @ X49 @ X48 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X47 ) @ ( u1_struct_0 @ X45 ) ) ) )
      | ~ ( v1_funct_2 @ X49 @ ( u1_struct_0 @ X47 ) @ ( u1_struct_0 @ X45 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_pre_topc @ X48 @ X47 )
      | ( v2_struct_0 @ X48 )
      | ~ ( l1_pre_topc @ X47 )
      | ~ ( v2_pre_topc @ X47 )
      | ( v2_struct_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t78_tmap_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','14','17','18','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( ( k2_tmap_1 @ X34 @ X32 @ X35 @ X33 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) @ X35 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('31',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_partfun1 @ X15 @ X16 @ X14 @ X17 )
        = ( k7_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','38','39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D ) ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','38','39','40'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v4_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('58',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_E ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['56','59'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( ( k7_relat_1 @ X2 @ X3 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) )
      = sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['57','58'])).

thf('64',plain,
    ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_D ) )
    = sk_E ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = sk_E )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['51','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
      = sk_E ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D )
    = sk_E ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('74',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_k3_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_pre_topc @ C @ A )
        & ( m1_pre_topc @ D @ A )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) )
     => ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
        & ( m1_subset_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X41 @ X43 @ X42 @ X40 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('79',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('85',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('92',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_funct_2 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('95',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('96',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('97',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X41 @ X43 @ X42 @ X40 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('100',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('106',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('114',plain,(
    m1_pre_topc @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['1','2'])).

thf('115',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('116',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ~ ( l1_pre_topc @ X43 )
      | ~ ( v2_pre_topc @ X43 )
      | ( v2_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X42 ) @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X41 @ X43 @ X42 @ X40 @ X44 ) @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('119',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('125',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['113','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','112','131'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['72','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('135',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('140',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('142',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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

thf('143',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X37 )
      | ~ ( l1_struct_0 @ X39 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X37 @ X38 @ X36 @ X39 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('146',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('147',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('150',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['144','147','150','151','152'])).

thf('154',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['141','153'])).

thf('155',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('156',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('157',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('159',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('161',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','161'])).

thf('163',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('164',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('165',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X37 )
      | ~ ( l1_struct_0 @ X39 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X37 @ X38 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['145','146'])).

thf('168',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['148','149'])).

thf('169',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170'])).

thf('172',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['163','171'])).

thf('173',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['159','160'])).

thf('174',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['133','140','162','174'])).

thf('176',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('177',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['177'])).

thf('179',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup+',[status(thm)],['176','180'])).

thf('182',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['4','5'])).

thf('183',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( ( k2_tmap_1 @ X34 @ X32 @ X35 @ X33 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) @ X35 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X35 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_G )
      | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_G @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('187',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('188',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_partfun1 @ X15 @ X16 @ X14 @ X17 )
        = ( k7_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_G @ X0 )
        = ( k7_relat_1 @ sk_G @ X0 ) )
      | ~ ( v1_funct_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0 )
        = ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['185','186','187','188','189','194','195','196'])).

thf('198',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ sk_C )
      = ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['182','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ sk_C )
      = ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ sk_C )
    = ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X37 )
      | ~ ( l1_struct_0 @ X39 )
      | ( m1_subset_1 @ ( k2_tmap_1 @ X37 @ X38 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_G )
      | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['145','146'])).

thf('207',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['148','149'])).

thf('208',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['205','206','207','208','209'])).

thf('211',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['202','210'])).

thf('212',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['159','160'])).

thf('213',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_funct_2 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      | ( ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_G @ X0 ) )
      | ~ ( v1_funct_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('222',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ sk_C )
    = ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('224',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( l1_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X37 )
      | ~ ( l1_struct_0 @ X39 )
      | ( v1_funct_2 @ ( k2_tmap_1 @ X37 @ X38 @ X36 @ X39 ) @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tmap_1])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_G )
      | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['145','146'])).

thf('228',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['148','149'])).

thf('229',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['226','227','228','229','230'])).

thf('232',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['223','231'])).

thf('233',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['159','160'])).

thf('234',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      | ( ( k7_relat_1 @ sk_G @ ( u1_struct_0 @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['215','222','234'])).

thf('236',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('240',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( X26 = X30 )
      | ~ ( r1_funct_2 @ X27 @ X28 @ X31 @ X29 @ X26 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('241',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('244',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_G )
    | ~ ( v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_G ) ),
    inference('sup-',[status(thm)],['238','244'])).

thf('246',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v1_funct_2 @ sk_G @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_G ) ),
    inference(demod,[status(thm)],['245','246','247','248'])).

thf('250',plain,
    ( ( sk_E = sk_G )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('251',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('252',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['148','149'])).

thf('254',plain,
    ( ( sk_E = sk_G )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['254','255'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ X0 )
      | ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['235','256','257'])).

thf('259',plain,
    ( ( ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
        = sk_F ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['181','258'])).

thf('260',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['264'])).

thf('266',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['254','255'])).

thf('267',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['177'])).

thf('268',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['267','268'])).

thf('270',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['266','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ X0 )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['93','112','131'])).

thf('272',plain,
    ( ( ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
        = sk_F ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['272','273','274','275'])).

thf('277',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['71'])).

thf('278',plain,
    ( ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['276','277'])).

thf('279',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170'])).

thf('280',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_funct_2 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('282',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ X0 )
      | ( sk_F = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ X0 )
      | ( sk_F = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['282','283','284'])).

thf('286',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_F
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['279','285'])).

thf('287',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['159','160'])).

thf('288',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('289',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('290',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('291',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('292',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('293',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( sk_F
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['286','287','288','289','290','291','292'])).

thf('294',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','161'])).

thf('295',plain,
    ( ( sk_F
      = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['293','294'])).

thf('296',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D )
      | ( sk_F
        = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['278','295'])).

thf('297',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('298',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(split,[status(esa)],['264'])).

thf('299',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['298','299'])).

thf('301',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference('sup-',[status(thm)],['297','300'])).

thf('302',plain,
    ( ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['296','301'])).

thf('303',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_funct_2 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('305',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_funct_2 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['304'])).

thf('306',plain,
    ( ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['303','305'])).

thf('307',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['306','307','308'])).

thf('310',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['302','309'])).

thf('311',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['310','311'])).

thf('313',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
      & ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['312','313'])).

thf('315',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['177'])).

thf('318',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ),
    inference('sat_resolution*',[status(thm)],['265','316','317'])).

thf('319',plain,
    ( ( k7_relat_1 @ sk_E @ ( u1_struct_0 @ sk_C ) )
    = sk_F ),
    inference(simpl_trail,[status(thm)],['263','318'])).

thf('320',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E )
      = sk_F ) ),
    inference(demod,[status(thm)],['175','319'])).

thf('321',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['264'])).

thf('322',plain,(
    sk_D = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['321','322'])).

thf('324',plain,(
    sk_E = sk_G ),
    inference(clc,[status(thm)],['254','255'])).

thf('325',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['323','324'])).

thf('326',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['265','316'])).

thf('327',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['325','326'])).

thf('328',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['320','327'])).

thf('329',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_F @ sk_F ),
    inference(demod,[status(thm)],['306','307','308'])).

thf('330',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['328','329'])).

thf('331',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['330','331'])).

thf('333',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['332','333'])).

thf('335',plain,(
    $false ),
    inference(demod,[status(thm)],['0','334'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MAkn7gkj30
% 0.16/0.36  % Computer   : n023.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 12:44:36 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 1.81/2.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.81/2.02  % Solved by: fo/fo7.sh
% 1.81/2.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.81/2.02  % done 4315 iterations in 1.539s
% 1.81/2.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.81/2.02  % SZS output start Refutation
% 1.81/2.02  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.81/2.02  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.81/2.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.81/2.02  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.81/2.02  thf(sk_C_type, type, sk_C: $i).
% 1.81/2.02  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.81/2.02  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.81/2.02  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.81/2.02  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.81/2.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.81/2.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.81/2.02  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 1.81/2.02  thf(sk_E_type, type, sk_E: $i).
% 1.81/2.02  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 1.81/2.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.81/2.02  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 1.81/2.02  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.81/2.02  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.81/2.02  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 1.81/2.02  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.81/2.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.81/2.02  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.81/2.02  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.81/2.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.81/2.02  thf(sk_D_type, type, sk_D: $i).
% 1.81/2.02  thf(sk_F_type, type, sk_F: $i).
% 1.81/2.02  thf(sk_A_type, type, sk_A: $i).
% 1.81/2.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.81/2.02  thf(sk_G_type, type, sk_G: $i).
% 1.81/2.02  thf(sk_B_type, type, sk_B: $i).
% 1.81/2.02  thf(t80_tmap_1, conjecture,
% 1.81/2.02    (![A:$i]:
% 1.81/2.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.81/2.02       ( ![B:$i]:
% 1.81/2.02         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.81/2.02             ( l1_pre_topc @ B ) ) =>
% 1.81/2.02           ( ![C:$i]:
% 1.81/2.02             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.81/2.02               ( ![D:$i]:
% 1.81/2.02                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.81/2.02                   ( ![E:$i]:
% 1.81/2.02                     ( ( ( v1_funct_1 @ E ) & 
% 1.81/2.02                         ( v1_funct_2 @
% 1.81/2.02                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.81/2.02                         ( m1_subset_1 @
% 1.81/2.02                           E @ 
% 1.81/2.02                           ( k1_zfmisc_1 @
% 1.81/2.02                             ( k2_zfmisc_1 @
% 1.81/2.02                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02                       ( ![F:$i]:
% 1.81/2.02                         ( ( ( v1_funct_1 @ F ) & 
% 1.81/2.02                             ( v1_funct_2 @
% 1.81/2.02                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.81/2.02                             ( m1_subset_1 @
% 1.81/2.02                               F @ 
% 1.81/2.02                               ( k1_zfmisc_1 @
% 1.81/2.02                                 ( k2_zfmisc_1 @
% 1.81/2.02                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02                           ( ![G:$i]:
% 1.81/2.02                             ( ( ( v1_funct_1 @ G ) & 
% 1.81/2.02                                 ( v1_funct_2 @
% 1.81/2.02                                   G @ ( u1_struct_0 @ D ) @ 
% 1.81/2.02                                   ( u1_struct_0 @ B ) ) & 
% 1.81/2.02                                 ( m1_subset_1 @
% 1.81/2.02                                   G @ 
% 1.81/2.02                                   ( k1_zfmisc_1 @
% 1.81/2.02                                     ( k2_zfmisc_1 @
% 1.81/2.02                                       ( u1_struct_0 @ D ) @ 
% 1.81/2.02                                       ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02                               ( ( ( ( D ) = ( A ) ) & 
% 1.81/2.02                                   ( r1_funct_2 @
% 1.81/2.02                                     ( u1_struct_0 @ A ) @ 
% 1.81/2.02                                     ( u1_struct_0 @ B ) @ 
% 1.81/2.02                                     ( u1_struct_0 @ D ) @ 
% 1.81/2.02                                     ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.81/2.02                                 ( ( r2_funct_2 @
% 1.81/2.02                                     ( u1_struct_0 @ C ) @ 
% 1.81/2.02                                     ( u1_struct_0 @ B ) @ 
% 1.81/2.02                                     ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.81/2.02                                   ( r2_funct_2 @
% 1.81/2.02                                     ( u1_struct_0 @ C ) @ 
% 1.81/2.02                                     ( u1_struct_0 @ B ) @ 
% 1.81/2.02                                     ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.81/2.02  thf(zf_stmt_0, negated_conjecture,
% 1.81/2.02    (~( ![A:$i]:
% 1.81/2.02        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.81/2.02            ( l1_pre_topc @ A ) ) =>
% 1.81/2.02          ( ![B:$i]:
% 1.81/2.02            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.81/2.02                ( l1_pre_topc @ B ) ) =>
% 1.81/2.02              ( ![C:$i]:
% 1.81/2.02                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.81/2.02                  ( ![D:$i]:
% 1.81/2.02                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.81/2.02                      ( ![E:$i]:
% 1.81/2.02                        ( ( ( v1_funct_1 @ E ) & 
% 1.81/2.02                            ( v1_funct_2 @
% 1.81/2.02                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.81/2.02                            ( m1_subset_1 @
% 1.81/2.02                              E @ 
% 1.81/2.02                              ( k1_zfmisc_1 @
% 1.81/2.02                                ( k2_zfmisc_1 @
% 1.81/2.02                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02                          ( ![F:$i]:
% 1.81/2.02                            ( ( ( v1_funct_1 @ F ) & 
% 1.81/2.02                                ( v1_funct_2 @
% 1.81/2.02                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.81/2.02                                ( m1_subset_1 @
% 1.81/2.02                                  F @ 
% 1.81/2.02                                  ( k1_zfmisc_1 @
% 1.81/2.02                                    ( k2_zfmisc_1 @
% 1.81/2.02                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02                              ( ![G:$i]:
% 1.81/2.02                                ( ( ( v1_funct_1 @ G ) & 
% 1.81/2.02                                    ( v1_funct_2 @
% 1.81/2.02                                      G @ ( u1_struct_0 @ D ) @ 
% 1.81/2.02                                      ( u1_struct_0 @ B ) ) & 
% 1.81/2.02                                    ( m1_subset_1 @
% 1.81/2.02                                      G @ 
% 1.81/2.02                                      ( k1_zfmisc_1 @
% 1.81/2.02                                        ( k2_zfmisc_1 @
% 1.81/2.02                                          ( u1_struct_0 @ D ) @ 
% 1.81/2.02                                          ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02                                  ( ( ( ( D ) = ( A ) ) & 
% 1.81/2.02                                      ( r1_funct_2 @
% 1.81/2.02                                        ( u1_struct_0 @ A ) @ 
% 1.81/2.02                                        ( u1_struct_0 @ B ) @ 
% 1.81/2.02                                        ( u1_struct_0 @ D ) @ 
% 1.81/2.02                                        ( u1_struct_0 @ B ) @ E @ G ) ) =>
% 1.81/2.02                                    ( ( r2_funct_2 @
% 1.81/2.02                                        ( u1_struct_0 @ C ) @ 
% 1.81/2.02                                        ( u1_struct_0 @ B ) @ 
% 1.81/2.02                                        ( k3_tmap_1 @ A @ B @ D @ C @ G ) @ F ) <=>
% 1.81/2.02                                      ( r2_funct_2 @
% 1.81/2.02                                        ( u1_struct_0 @ C ) @ 
% 1.81/2.02                                        ( u1_struct_0 @ B ) @ 
% 1.81/2.02                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.81/2.02    inference('cnf.neg', [status(esa)], [t80_tmap_1])).
% 1.81/2.02  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('2', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('3', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['1', '2'])).
% 1.81/2.02  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('5', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('6', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['4', '5'])).
% 1.81/2.02  thf('7', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('8', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('9', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(t78_tmap_1, axiom,
% 1.81/2.02    (![A:$i]:
% 1.81/2.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.81/2.02       ( ![B:$i]:
% 1.81/2.02         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.81/2.02             ( l1_pre_topc @ B ) ) =>
% 1.81/2.02           ( ![C:$i]:
% 1.81/2.02             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.81/2.02               ( ![D:$i]:
% 1.81/2.02                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.81/2.02                   ( ![E:$i]:
% 1.81/2.02                     ( ( ( v1_funct_1 @ E ) & 
% 1.81/2.02                         ( v1_funct_2 @
% 1.81/2.02                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.81/2.02                         ( m1_subset_1 @
% 1.81/2.02                           E @ 
% 1.81/2.02                           ( k1_zfmisc_1 @
% 1.81/2.02                             ( k2_zfmisc_1 @
% 1.81/2.02                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02                       ( ( m1_pre_topc @ C @ D ) =>
% 1.81/2.02                         ( r2_funct_2 @
% 1.81/2.02                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 1.81/2.02                           ( k3_tmap_1 @
% 1.81/2.02                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 1.81/2.02                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.81/2.02  thf('10', plain,
% 1.81/2.02      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 1.81/2.02         ((v2_struct_0 @ X45)
% 1.81/2.02          | ~ (v2_pre_topc @ X45)
% 1.81/2.02          | ~ (l1_pre_topc @ X45)
% 1.81/2.02          | (v2_struct_0 @ X46)
% 1.81/2.02          | ~ (m1_pre_topc @ X46 @ X47)
% 1.81/2.02          | ~ (m1_pre_topc @ X48 @ X46)
% 1.81/2.02          | (r2_funct_2 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X45) @ 
% 1.81/2.02             (k3_tmap_1 @ X47 @ X45 @ X46 @ X48 @ 
% 1.81/2.02              (k2_tmap_1 @ X47 @ X45 @ X49 @ X46)) @ 
% 1.81/2.02             (k2_tmap_1 @ X47 @ X45 @ X49 @ X48))
% 1.81/2.02          | ~ (m1_subset_1 @ X49 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ X47) @ (u1_struct_0 @ X45))))
% 1.81/2.02          | ~ (v1_funct_2 @ X49 @ (u1_struct_0 @ X47) @ (u1_struct_0 @ X45))
% 1.81/2.02          | ~ (v1_funct_1 @ X49)
% 1.81/2.02          | ~ (m1_pre_topc @ X48 @ X47)
% 1.81/2.02          | (v2_struct_0 @ X48)
% 1.81/2.02          | ~ (l1_pre_topc @ X47)
% 1.81/2.02          | ~ (v2_pre_topc @ X47)
% 1.81/2.02          | (v2_struct_0 @ X47))),
% 1.81/2.02      inference('cnf', [status(esa)], [t78_tmap_1])).
% 1.81/2.02  thf('11', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_D)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_D)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ X0)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ 
% 1.81/2.02              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)) @ 
% 1.81/2.02             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ X1)
% 1.81/2.02          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ X1)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_B)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_B)
% 1.81/2.02          | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('sup-', [status(thm)], ['9', '10'])).
% 1.81/2.02  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('13', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('14', plain, ((v2_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['12', '13'])).
% 1.81/2.02  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('16', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.02  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('19', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('20', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('21', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.02  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('24', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ X0)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k3_tmap_1 @ sk_D @ sk_B @ X1 @ X0 @ 
% 1.81/2.02              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X1)) @ 
% 1.81/2.02             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0))
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ X1)
% 1.81/2.02          | ~ (m1_pre_topc @ X1 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ X1)
% 1.81/2.02          | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)],
% 1.81/2.02                ['11', '14', '17', '18', '21', '22', '23'])).
% 1.81/2.02  thf('25', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_B)
% 1.81/2.02          | (v2_struct_0 @ X0)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.81/2.02          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ 
% 1.81/2.02              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)) @ 
% 1.81/2.02             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.81/2.02          | (v2_struct_0 @ sk_C)
% 1.81/2.02          | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('sup-', [status(thm)], ['6', '24'])).
% 1.81/2.02  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['4', '5'])).
% 1.81/2.02  thf('27', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(d4_tmap_1, axiom,
% 1.81/2.02    (![A:$i]:
% 1.81/2.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.81/2.02       ( ![B:$i]:
% 1.81/2.02         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 1.81/2.02             ( l1_pre_topc @ B ) ) =>
% 1.81/2.02           ( ![C:$i]:
% 1.81/2.02             ( ( ( v1_funct_1 @ C ) & 
% 1.81/2.02                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.81/2.02                 ( m1_subset_1 @
% 1.81/2.02                   C @ 
% 1.81/2.02                   ( k1_zfmisc_1 @
% 1.81/2.02                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02               ( ![D:$i]:
% 1.81/2.02                 ( ( m1_pre_topc @ D @ A ) =>
% 1.81/2.02                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 1.81/2.02                     ( k2_partfun1 @
% 1.81/2.02                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 1.81/2.02                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 1.81/2.02  thf('28', plain,
% 1.81/2.02      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.81/2.02         ((v2_struct_0 @ X32)
% 1.81/2.02          | ~ (v2_pre_topc @ X32)
% 1.81/2.02          | ~ (l1_pre_topc @ X32)
% 1.81/2.02          | ~ (m1_pre_topc @ X33 @ X34)
% 1.81/2.02          | ((k2_tmap_1 @ X34 @ X32 @ X35 @ X33)
% 1.81/2.02              = (k2_partfun1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32) @ 
% 1.81/2.02                 X35 @ (u1_struct_0 @ X33)))
% 1.81/2.02          | ~ (m1_subset_1 @ X35 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))))
% 1.81/2.02          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))
% 1.81/2.02          | ~ (v1_funct_1 @ X35)
% 1.81/2.02          | ~ (l1_pre_topc @ X34)
% 1.81/2.02          | ~ (v2_pre_topc @ X34)
% 1.81/2.02          | (v2_struct_0 @ X34))),
% 1.81/2.02      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.81/2.02  thf('29', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_D)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_D)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_D)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.81/2.02              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02                 sk_E @ (u1_struct_0 @ X0)))
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_B)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_B)
% 1.81/2.02          | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('sup-', [status(thm)], ['27', '28'])).
% 1.81/2.02  thf('30', plain, ((v2_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['12', '13'])).
% 1.81/2.02  thf('31', plain, ((l1_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.02  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('33', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.02  thf('34', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(redefinition_k2_partfun1, axiom,
% 1.81/2.02    (![A:$i,B:$i,C:$i,D:$i]:
% 1.81/2.02     ( ( ( v1_funct_1 @ C ) & 
% 1.81/2.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.81/2.02       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.81/2.02  thf('35', plain,
% 1.81/2.02      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.81/2.02          | ~ (v1_funct_1 @ X14)
% 1.81/2.02          | ((k2_partfun1 @ X15 @ X16 @ X14 @ X17) = (k7_relat_1 @ X14 @ X17)))),
% 1.81/2.02      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.81/2.02  thf('36', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.81/2.02            X0) = (k7_relat_1 @ sk_E @ X0))
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E))),
% 1.81/2.02      inference('sup-', [status(thm)], ['34', '35'])).
% 1.81/2.02  thf('37', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('38', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.81/2.02           X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['36', '37'])).
% 1.81/2.02  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('41', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_D)
% 1.81/2.02          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.81/2.02              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)],
% 1.81/2.02                ['29', '30', '31', '32', '33', '38', '39', '40'])).
% 1.81/2.02  thf('42', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('sup-', [status(thm)], ['26', '41'])).
% 1.81/2.02  thf('43', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('44', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_D)
% 1.81/2.02        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.81/2.02      inference('clc', [status(thm)], ['42', '43'])).
% 1.81/2.02  thf('45', plain, (~ (v2_struct_0 @ sk_D)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('46', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('47', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_B)
% 1.81/2.02          | (v2_struct_0 @ X0)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | ~ (m1_pre_topc @ sk_C @ X0)
% 1.81/2.02          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k3_tmap_1 @ sk_D @ sk_B @ X0 @ sk_C @ 
% 1.81/2.02              (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)) @ 
% 1.81/2.02             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02          | (v2_struct_0 @ sk_C)
% 1.81/2.02          | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('demod', [status(thm)], ['25', '46'])).
% 1.81/2.02  thf('48', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_C)
% 1.81/2.02        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 1.81/2.02            (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)) @ 
% 1.81/2.02           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('sup-', [status(thm)], ['3', '47'])).
% 1.81/2.02  thf('49', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['1', '2'])).
% 1.81/2.02  thf('50', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_D)
% 1.81/2.02          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 1.81/2.02              = (k7_relat_1 @ sk_E @ (u1_struct_0 @ X0)))
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)],
% 1.81/2.02                ['29', '30', '31', '32', '33', '38', '39', '40'])).
% 1.81/2.02  thf('51', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D)
% 1.81/2.02            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)))
% 1.81/2.02        | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('sup-', [status(thm)], ['49', '50'])).
% 1.81/2.02  thf('52', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(cc2_relset_1, axiom,
% 1.81/2.02    (![A:$i,B:$i,C:$i]:
% 1.81/2.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.81/2.02       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.81/2.02  thf('53', plain,
% 1.81/2.02      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.81/2.02         ((v4_relat_1 @ X7 @ X8)
% 1.81/2.02          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.81/2.02      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.81/2.02  thf('54', plain, ((v4_relat_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 1.81/2.02      inference('sup-', [status(thm)], ['52', '53'])).
% 1.81/2.02  thf(d18_relat_1, axiom,
% 1.81/2.02    (![A:$i,B:$i]:
% 1.81/2.02     ( ( v1_relat_1 @ B ) =>
% 1.81/2.02       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.81/2.02  thf('55', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         (~ (v4_relat_1 @ X0 @ X1)
% 1.81/2.02          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.81/2.02          | ~ (v1_relat_1 @ X0))),
% 1.81/2.02      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.81/2.02  thf('56', plain,
% 1.81/2.02      ((~ (v1_relat_1 @ sk_E)
% 1.81/2.02        | (r1_tarski @ (k1_relat_1 @ sk_E) @ (u1_struct_0 @ sk_D)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['54', '55'])).
% 1.81/2.02  thf('57', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(cc1_relset_1, axiom,
% 1.81/2.02    (![A:$i,B:$i,C:$i]:
% 1.81/2.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.81/2.02       ( v1_relat_1 @ C ) ))).
% 1.81/2.02  thf('58', plain,
% 1.81/2.02      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.81/2.02         ((v1_relat_1 @ X4)
% 1.81/2.02          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.81/2.02      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.81/2.02  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 1.81/2.02      inference('sup-', [status(thm)], ['57', '58'])).
% 1.81/2.02  thf('60', plain, ((r1_tarski @ (k1_relat_1 @ sk_E) @ (u1_struct_0 @ sk_D))),
% 1.81/2.02      inference('demod', [status(thm)], ['56', '59'])).
% 1.81/2.02  thf(t97_relat_1, axiom,
% 1.81/2.02    (![A:$i,B:$i]:
% 1.81/2.02     ( ( v1_relat_1 @ B ) =>
% 1.81/2.02       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.81/2.02         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.81/2.02  thf('61', plain,
% 1.81/2.02      (![X2 : $i, X3 : $i]:
% 1.81/2.02         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 1.81/2.02          | ((k7_relat_1 @ X2 @ X3) = (X2))
% 1.81/2.02          | ~ (v1_relat_1 @ X2))),
% 1.81/2.02      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.81/2.02  thf('62', plain,
% 1.81/2.02      ((~ (v1_relat_1 @ sk_E)
% 1.81/2.02        | ((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)) = (sk_E)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['60', '61'])).
% 1.81/2.02  thf('63', plain, ((v1_relat_1 @ sk_E)),
% 1.81/2.02      inference('sup-', [status(thm)], ['57', '58'])).
% 1.81/2.02  thf('64', plain, (((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_D)) = (sk_E))),
% 1.81/2.02      inference('demod', [status(thm)], ['62', '63'])).
% 1.81/2.02  thf('65', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))
% 1.81/2.02        | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('demod', [status(thm)], ['51', '64'])).
% 1.81/2.02  thf('66', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('67', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_D)
% 1.81/2.02        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E)))),
% 1.81/2.02      inference('clc', [status(thm)], ['65', '66'])).
% 1.81/2.02  thf('68', plain, (~ (v2_struct_0 @ sk_D)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('69', plain, (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_D) = (sk_E))),
% 1.81/2.02      inference('clc', [status(thm)], ['67', '68'])).
% 1.81/2.02  thf('70', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['4', '5'])).
% 1.81/2.02  thf('71', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_C)
% 1.81/2.02        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | (v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['48', '69', '70'])).
% 1.81/2.02  thf('72', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | (v2_struct_0 @ sk_C)
% 1.81/2.02        | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('simplify', [status(thm)], ['71'])).
% 1.81/2.02  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['4', '5'])).
% 1.81/2.02  thf('74', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['1', '2'])).
% 1.81/2.02  thf('75', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(dt_k3_tmap_1, axiom,
% 1.81/2.02    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.81/2.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.81/2.02         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 1.81/2.02         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 1.81/2.02         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 1.81/2.02         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 1.81/2.02         ( m1_subset_1 @
% 1.81/2.02           E @ 
% 1.81/2.02           ( k1_zfmisc_1 @
% 1.81/2.02             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.81/2.02       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 1.81/2.02         ( v1_funct_2 @
% 1.81/2.02           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 1.81/2.02           ( u1_struct_0 @ B ) ) & 
% 1.81/2.02         ( m1_subset_1 @
% 1.81/2.02           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 1.81/2.02           ( k1_zfmisc_1 @
% 1.81/2.02             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.81/2.02  thf('76', plain,
% 1.81/2.02      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X40 @ X41)
% 1.81/2.02          | ~ (m1_pre_topc @ X42 @ X41)
% 1.81/2.02          | ~ (l1_pre_topc @ X43)
% 1.81/2.02          | ~ (v2_pre_topc @ X43)
% 1.81/2.02          | (v2_struct_0 @ X43)
% 1.81/2.02          | ~ (l1_pre_topc @ X41)
% 1.81/2.02          | ~ (v2_pre_topc @ X41)
% 1.81/2.02          | (v2_struct_0 @ X41)
% 1.81/2.02          | ~ (v1_funct_1 @ X44)
% 1.81/2.02          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X43))
% 1.81/2.02          | ~ (m1_subset_1 @ X44 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X43))))
% 1.81/2.02          | (m1_subset_1 @ (k3_tmap_1 @ X41 @ X43 @ X42 @ X40 @ X44) @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X43)))))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.81/2.02  thf('77', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.81/2.02           (k1_zfmisc_1 @ 
% 1.81/2.02            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E)
% 1.81/2.02          | (v2_struct_0 @ X1)
% 1.81/2.02          | ~ (v2_pre_topc @ X1)
% 1.81/2.02          | ~ (l1_pre_topc @ X1)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_B)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_B)
% 1.81/2.02          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.81/2.02      inference('sup-', [status(thm)], ['75', '76'])).
% 1.81/2.02  thf('78', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.02  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('80', plain, ((v2_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('82', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.81/2.02           (k1_zfmisc_1 @ 
% 1.81/2.02            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | (v2_struct_0 @ X1)
% 1.81/2.02          | ~ (v2_pre_topc @ X1)
% 1.81/2.02          | ~ (l1_pre_topc @ X1)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.81/2.02      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 1.81/2.02  thf('83', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_D)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_D)
% 1.81/2.02          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.81/2.02      inference('sup-', [status(thm)], ['74', '82'])).
% 1.81/2.02  thf('84', plain, ((l1_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.02  thf('85', plain, ((v2_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['12', '13'])).
% 1.81/2.02  thf('86', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | (v2_struct_0 @ sk_D)
% 1.81/2.02          | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 1.81/2.02      inference('demod', [status(thm)], ['83', '84', '85'])).
% 1.81/2.02  thf('87', plain,
% 1.81/2.02      (((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02         (k1_zfmisc_1 @ 
% 1.81/2.02          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02        | (v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('sup-', [status(thm)], ['73', '86'])).
% 1.81/2.02  thf('88', plain, (~ (v2_struct_0 @ sk_D)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('89', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | (m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02           (k1_zfmisc_1 @ 
% 1.81/2.02            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 1.81/2.02      inference('clc', [status(thm)], ['87', '88'])).
% 1.81/2.02  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('91', plain,
% 1.81/2.02      ((m1_subset_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('clc', [status(thm)], ['89', '90'])).
% 1.81/2.02  thf(redefinition_r2_funct_2, axiom,
% 1.81/2.02    (![A:$i,B:$i,C:$i,D:$i]:
% 1.81/2.02     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.81/2.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.81/2.02         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.81/2.02         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.81/2.02       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.81/2.02  thf('92', plain,
% 1.81/2.02      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.81/2.02          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 1.81/2.02          | ~ (v1_funct_1 @ X18)
% 1.81/2.02          | ~ (v1_funct_1 @ X21)
% 1.81/2.02          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.81/2.02          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.81/2.02          | ((X18) = (X21))
% 1.81/2.02          | ~ (r2_funct_2 @ X19 @ X20 @ X18 @ X21))),
% 1.81/2.02      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.81/2.02  thf('93', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.81/2.02          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ X0)
% 1.81/2.02          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 1.81/2.02          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['91', '92'])).
% 1.81/2.02  thf('94', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['4', '5'])).
% 1.81/2.02  thf('95', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['1', '2'])).
% 1.81/2.02  thf('96', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf('97', plain,
% 1.81/2.02      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X40 @ X41)
% 1.81/2.02          | ~ (m1_pre_topc @ X42 @ X41)
% 1.81/2.02          | ~ (l1_pre_topc @ X43)
% 1.81/2.02          | ~ (v2_pre_topc @ X43)
% 1.81/2.02          | (v2_struct_0 @ X43)
% 1.81/2.02          | ~ (l1_pre_topc @ X41)
% 1.81/2.02          | ~ (v2_pre_topc @ X41)
% 1.81/2.02          | (v2_struct_0 @ X41)
% 1.81/2.02          | ~ (v1_funct_1 @ X44)
% 1.81/2.02          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X43))
% 1.81/2.02          | ~ (m1_subset_1 @ X44 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X43))))
% 1.81/2.02          | (v1_funct_1 @ (k3_tmap_1 @ X41 @ X43 @ X42 @ X40 @ X44)))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.81/2.02  thf('98', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E))
% 1.81/2.02          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E)
% 1.81/2.02          | (v2_struct_0 @ X1)
% 1.81/2.02          | ~ (v2_pre_topc @ X1)
% 1.81/2.02          | ~ (l1_pre_topc @ X1)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_B)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_B)
% 1.81/2.02          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.81/2.02      inference('sup-', [status(thm)], ['96', '97'])).
% 1.81/2.02  thf('99', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.02  thf('100', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('101', plain, ((v2_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('103', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E))
% 1.81/2.02          | (v2_struct_0 @ X1)
% 1.81/2.02          | ~ (v2_pre_topc @ X1)
% 1.81/2.02          | ~ (l1_pre_topc @ X1)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.81/2.02      inference('demod', [status(thm)], ['98', '99', '100', '101', '102'])).
% 1.81/2.02  thf('104', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_D)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_D)
% 1.81/2.02          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['95', '103'])).
% 1.81/2.02  thf('105', plain, ((l1_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.02  thf('106', plain, ((v2_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['12', '13'])).
% 1.81/2.02  thf('107', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | (v2_struct_0 @ sk_D)
% 1.81/2.02          | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E)))),
% 1.81/2.02      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.81/2.02  thf('108', plain,
% 1.81/2.02      (((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))
% 1.81/2.02        | (v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('sup-', [status(thm)], ['94', '107'])).
% 1.81/2.02  thf('109', plain, (~ (v2_struct_0 @ sk_D)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('110', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | (v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)))),
% 1.81/2.02      inference('clc', [status(thm)], ['108', '109'])).
% 1.81/2.02  thf('111', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('112', plain,
% 1.81/2.02      ((v1_funct_1 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E))),
% 1.81/2.02      inference('clc', [status(thm)], ['110', '111'])).
% 1.81/2.02  thf('113', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['4', '5'])).
% 1.81/2.02  thf('114', plain, ((m1_pre_topc @ sk_D @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['1', '2'])).
% 1.81/2.02  thf('115', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf('116', plain,
% 1.81/2.02      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X40 @ X41)
% 1.81/2.02          | ~ (m1_pre_topc @ X42 @ X41)
% 1.81/2.02          | ~ (l1_pre_topc @ X43)
% 1.81/2.02          | ~ (v2_pre_topc @ X43)
% 1.81/2.02          | (v2_struct_0 @ X43)
% 1.81/2.02          | ~ (l1_pre_topc @ X41)
% 1.81/2.02          | ~ (v2_pre_topc @ X41)
% 1.81/2.02          | (v2_struct_0 @ X41)
% 1.81/2.02          | ~ (v1_funct_1 @ X44)
% 1.81/2.02          | ~ (v1_funct_2 @ X44 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X43))
% 1.81/2.02          | ~ (m1_subset_1 @ X44 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ X42) @ (u1_struct_0 @ X43))))
% 1.81/2.02          | (v1_funct_2 @ (k3_tmap_1 @ X41 @ X43 @ X42 @ X40 @ X44) @ 
% 1.81/2.02             (u1_struct_0 @ X40) @ (u1_struct_0 @ X43)))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 1.81/2.02  thf('117', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.81/2.02           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E)
% 1.81/2.02          | (v2_struct_0 @ X1)
% 1.81/2.02          | ~ (v2_pre_topc @ X1)
% 1.81/2.02          | ~ (l1_pre_topc @ X1)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_B)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_B)
% 1.81/2.02          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.81/2.02      inference('sup-', [status(thm)], ['115', '116'])).
% 1.81/2.02  thf('118', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.02  thf('119', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('120', plain, ((v2_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('121', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('122', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i]:
% 1.81/2.02         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.81/2.02           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | (v2_struct_0 @ X1)
% 1.81/2.02          | ~ (v2_pre_topc @ X1)
% 1.81/2.02          | ~ (l1_pre_topc @ X1)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (m1_pre_topc @ sk_D @ X1)
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ X1))),
% 1.81/2.02      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 1.81/2.02  thf('123', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_D)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_D)
% 1.81/2.02          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.81/2.02             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['114', '122'])).
% 1.81/2.02  thf('124', plain, ((l1_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.02  thf('125', plain, ((v2_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['12', '13'])).
% 1.81/2.02  thf('126', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B)
% 1.81/2.02          | (v2_struct_0 @ sk_D)
% 1.81/2.02          | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ sk_E) @ 
% 1.81/2.02             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.81/2.02  thf('127', plain,
% 1.81/2.02      (((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | (v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('sup-', [status(thm)], ['113', '126'])).
% 1.81/2.02  thf('128', plain, (~ (v2_struct_0 @ sk_D)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('129', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | (v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('clc', [status(thm)], ['127', '128'])).
% 1.81/2.02  thf('130', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('131', plain,
% 1.81/2.02      ((v1_funct_2 @ (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('clc', [status(thm)], ['129', '130'])).
% 1.81/2.02  thf('132', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.81/2.02          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['93', '112', '131'])).
% 1.81/2.02  thf('133', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_C)
% 1.81/2.02        | (v2_struct_0 @ sk_B)
% 1.81/2.02        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | ~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.81/2.02            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.81/2.02      inference('sup-', [status(thm)], ['72', '132'])).
% 1.81/2.02  thf('134', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(dt_k2_partfun1, axiom,
% 1.81/2.02    (![A:$i,B:$i,C:$i,D:$i]:
% 1.81/2.02     ( ( ( v1_funct_1 @ C ) & 
% 1.81/2.02         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.81/2.02       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 1.81/2.02         ( m1_subset_1 @
% 1.81/2.02           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 1.81/2.02           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.81/2.02  thf('135', plain,
% 1.81/2.02      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.81/2.02          | ~ (v1_funct_1 @ X10)
% 1.81/2.02          | (v1_funct_1 @ (k2_partfun1 @ X11 @ X12 @ X10 @ X13)))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 1.81/2.02  thf('136', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v1_funct_1 @ 
% 1.81/2.02           (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.81/2.02            X0))
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E))),
% 1.81/2.02      inference('sup-', [status(thm)], ['134', '135'])).
% 1.81/2.02  thf('137', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('138', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (v1_funct_1 @ 
% 1.81/2.02          (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.81/2.02           X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['136', '137'])).
% 1.81/2.02  thf('139', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 1.81/2.02           X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['36', '37'])).
% 1.81/2.02  thf('140', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['138', '139'])).
% 1.81/2.02  thf('141', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('142', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(dt_k2_tmap_1, axiom,
% 1.81/2.02    (![A:$i,B:$i,C:$i,D:$i]:
% 1.81/2.02     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) & ( v1_funct_1 @ C ) & 
% 1.81/2.02         ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.81/2.02         ( m1_subset_1 @
% 1.81/2.02           C @ 
% 1.81/2.02           ( k1_zfmisc_1 @
% 1.81/2.02             ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) & 
% 1.81/2.02         ( l1_struct_0 @ D ) ) =>
% 1.81/2.02       ( ( v1_funct_1 @ ( k2_tmap_1 @ A @ B @ C @ D ) ) & 
% 1.81/2.02         ( v1_funct_2 @
% 1.81/2.02           ( k2_tmap_1 @ A @ B @ C @ D ) @ ( u1_struct_0 @ D ) @ 
% 1.81/2.02           ( u1_struct_0 @ B ) ) & 
% 1.81/2.02         ( m1_subset_1 @
% 1.81/2.02           ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 1.81/2.02           ( k1_zfmisc_1 @
% 1.81/2.02             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.81/2.02  thf('143', plain,
% 1.81/2.02      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X36 @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 1.81/2.02          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.81/2.02          | ~ (v1_funct_1 @ X36)
% 1.81/2.02          | ~ (l1_struct_0 @ X38)
% 1.81/2.02          | ~ (l1_struct_0 @ X37)
% 1.81/2.02          | ~ (l1_struct_0 @ X39)
% 1.81/2.02          | (v1_funct_2 @ (k2_tmap_1 @ X37 @ X38 @ X36 @ X39) @ 
% 1.81/2.02             (u1_struct_0 @ X39) @ (u1_struct_0 @ X38)))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.81/2.02  thf('144', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.81/2.02           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (l1_struct_0 @ X0)
% 1.81/2.02          | ~ (l1_struct_0 @ sk_D)
% 1.81/2.02          | ~ (l1_struct_0 @ sk_B)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['142', '143'])).
% 1.81/2.02  thf('145', plain, ((l1_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.02  thf(dt_l1_pre_topc, axiom,
% 1.81/2.02    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.81/2.02  thf('146', plain,
% 1.81/2.02      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.02  thf('147', plain, ((l1_struct_0 @ sk_D)),
% 1.81/2.02      inference('sup-', [status(thm)], ['145', '146'])).
% 1.81/2.02  thf('148', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('149', plain,
% 1.81/2.02      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.02  thf('150', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.02      inference('sup-', [status(thm)], ['148', '149'])).
% 1.81/2.02  thf('151', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('152', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.02  thf('153', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.81/2.02           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (l1_struct_0 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['144', '147', '150', '151', '152'])).
% 1.81/2.02  thf('154', plain,
% 1.81/2.02      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ~ (l1_struct_0 @ sk_C))),
% 1.81/2.02      inference('sup+', [status(thm)], ['141', '153'])).
% 1.81/2.02  thf('155', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['4', '5'])).
% 1.81/2.02  thf(dt_m1_pre_topc, axiom,
% 1.81/2.02    (![A:$i]:
% 1.81/2.02     ( ( l1_pre_topc @ A ) =>
% 1.81/2.02       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.81/2.02  thf('156', plain,
% 1.81/2.02      (![X23 : $i, X24 : $i]:
% 1.81/2.02         (~ (m1_pre_topc @ X23 @ X24)
% 1.81/2.02          | (l1_pre_topc @ X23)
% 1.81/2.02          | ~ (l1_pre_topc @ X24))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.81/2.02  thf('157', plain, ((~ (l1_pre_topc @ sk_D) | (l1_pre_topc @ sk_C))),
% 1.81/2.02      inference('sup-', [status(thm)], ['155', '156'])).
% 1.81/2.02  thf('158', plain, ((l1_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.02  thf('159', plain, ((l1_pre_topc @ sk_C)),
% 1.81/2.02      inference('demod', [status(thm)], ['157', '158'])).
% 1.81/2.02  thf('160', plain,
% 1.81/2.02      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.81/2.02  thf('161', plain, ((l1_struct_0 @ sk_C)),
% 1.81/2.02      inference('sup-', [status(thm)], ['159', '160'])).
% 1.81/2.02  thf('162', plain,
% 1.81/2.02      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['154', '161'])).
% 1.81/2.02  thf('163', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('164', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf('165', plain,
% 1.81/2.02      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X36 @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 1.81/2.02          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.81/2.02          | ~ (v1_funct_1 @ X36)
% 1.81/2.02          | ~ (l1_struct_0 @ X38)
% 1.81/2.02          | ~ (l1_struct_0 @ X37)
% 1.81/2.02          | ~ (l1_struct_0 @ X39)
% 1.81/2.02          | (m1_subset_1 @ (k2_tmap_1 @ X37 @ X38 @ X36 @ X39) @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38)))))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.81/2.02  thf('166', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.81/2.02           (k1_zfmisc_1 @ 
% 1.81/2.02            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (l1_struct_0 @ X0)
% 1.81/2.02          | ~ (l1_struct_0 @ sk_D)
% 1.81/2.02          | ~ (l1_struct_0 @ sk_B)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['164', '165'])).
% 1.81/2.02  thf('167', plain, ((l1_struct_0 @ sk_D)),
% 1.81/2.02      inference('sup-', [status(thm)], ['145', '146'])).
% 1.81/2.02  thf('168', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.02      inference('sup-', [status(thm)], ['148', '149'])).
% 1.81/2.02  thf('169', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('170', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.02  thf('171', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.81/2.02           (k1_zfmisc_1 @ 
% 1.81/2.02            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (l1_struct_0 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['166', '167', '168', '169', '170'])).
% 1.81/2.02  thf('172', plain,
% 1.81/2.02      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02         (k1_zfmisc_1 @ 
% 1.81/2.02          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02        | ~ (l1_struct_0 @ sk_C))),
% 1.81/2.02      inference('sup+', [status(thm)], ['163', '171'])).
% 1.81/2.02  thf('173', plain, ((l1_struct_0 @ sk_C)),
% 1.81/2.02      inference('sup-', [status(thm)], ['159', '160'])).
% 1.81/2.02  thf('174', plain,
% 1.81/2.02      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['172', '173'])).
% 1.81/2.02  thf('175', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_C)
% 1.81/2.02        | (v2_struct_0 @ sk_B)
% 1.81/2.02        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E)
% 1.81/2.02            = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.81/2.02      inference('demod', [status(thm)], ['133', '140', '162', '174'])).
% 1.81/2.02  thf('176', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('177', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.81/2.02        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('178', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.81/2.02      inference('split', [status(esa)], ['177'])).
% 1.81/2.02  thf('179', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('180', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['178', '179'])).
% 1.81/2.02  thf('181', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.81/2.02      inference('sup+', [status(thm)], ['176', '180'])).
% 1.81/2.02  thf('182', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['4', '5'])).
% 1.81/2.02  thf('183', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_G @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('184', plain,
% 1.81/2.02      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.81/2.02         ((v2_struct_0 @ X32)
% 1.81/2.02          | ~ (v2_pre_topc @ X32)
% 1.81/2.02          | ~ (l1_pre_topc @ X32)
% 1.81/2.02          | ~ (m1_pre_topc @ X33 @ X34)
% 1.81/2.02          | ((k2_tmap_1 @ X34 @ X32 @ X35 @ X33)
% 1.81/2.02              = (k2_partfun1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32) @ 
% 1.81/2.02                 X35 @ (u1_struct_0 @ X33)))
% 1.81/2.02          | ~ (m1_subset_1 @ X35 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))))
% 1.81/2.02          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))
% 1.81/2.02          | ~ (v1_funct_1 @ X35)
% 1.81/2.02          | ~ (l1_pre_topc @ X34)
% 1.81/2.02          | ~ (v2_pre_topc @ X34)
% 1.81/2.02          | (v2_struct_0 @ X34))),
% 1.81/2.02      inference('cnf', [status(esa)], [d4_tmap_1])).
% 1.81/2.02  thf('185', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_D)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_D)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_D)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_G)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0)
% 1.81/2.02              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02                 sk_G @ (u1_struct_0 @ X0)))
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | ~ (l1_pre_topc @ sk_B)
% 1.81/2.02          | ~ (v2_pre_topc @ sk_B)
% 1.81/2.02          | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('sup-', [status(thm)], ['183', '184'])).
% 1.81/2.02  thf('186', plain, ((v2_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['12', '13'])).
% 1.81/2.02  thf('187', plain, ((l1_pre_topc @ sk_D)),
% 1.81/2.02      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.02  thf('188', plain, ((v1_funct_1 @ sk_G)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('189', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('190', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_G @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('191', plain,
% 1.81/2.02      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.81/2.02          | ~ (v1_funct_1 @ X14)
% 1.81/2.02          | ((k2_partfun1 @ X15 @ X16 @ X14 @ X17) = (k7_relat_1 @ X14 @ X17)))),
% 1.81/2.02      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.81/2.02  thf('192', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_G @ 
% 1.81/2.02            X0) = (k7_relat_1 @ sk_G @ X0))
% 1.81/2.02          | ~ (v1_funct_1 @ sk_G))),
% 1.81/2.02      inference('sup-', [status(thm)], ['190', '191'])).
% 1.81/2.02  thf('193', plain, ((v1_funct_1 @ sk_G)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('194', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_G @ 
% 1.81/2.02           X0) = (k7_relat_1 @ sk_G @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['192', '193'])).
% 1.81/2.02  thf('195', plain, ((l1_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('196', plain, ((v2_pre_topc @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('197', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v2_struct_0 @ sk_D)
% 1.81/2.02          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0)
% 1.81/2.02              = (k7_relat_1 @ sk_G @ (u1_struct_0 @ X0)))
% 1.81/2.02          | ~ (m1_pre_topc @ X0 @ sk_D)
% 1.81/2.02          | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)],
% 1.81/2.02                ['185', '186', '187', '188', '189', '194', '195', '196'])).
% 1.81/2.02  thf('198', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_G @ sk_C)
% 1.81/2.02            = (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('sup-', [status(thm)], ['182', '197'])).
% 1.81/2.02  thf('199', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('200', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_D)
% 1.81/2.02        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_G @ sk_C)
% 1.81/2.02            = (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C))))),
% 1.81/2.02      inference('clc', [status(thm)], ['198', '199'])).
% 1.81/2.02  thf('201', plain, (~ (v2_struct_0 @ sk_D)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('202', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_G @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['200', '201'])).
% 1.81/2.02  thf('203', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_G @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('204', plain,
% 1.81/2.02      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X36 @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 1.81/2.02          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.81/2.02          | ~ (v1_funct_1 @ X36)
% 1.81/2.02          | ~ (l1_struct_0 @ X38)
% 1.81/2.02          | ~ (l1_struct_0 @ X37)
% 1.81/2.02          | ~ (l1_struct_0 @ X39)
% 1.81/2.02          | (m1_subset_1 @ (k2_tmap_1 @ X37 @ X38 @ X36 @ X39) @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38)))))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.81/2.02  thf('205', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0) @ 
% 1.81/2.02           (k1_zfmisc_1 @ 
% 1.81/2.02            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (l1_struct_0 @ X0)
% 1.81/2.02          | ~ (l1_struct_0 @ sk_D)
% 1.81/2.02          | ~ (l1_struct_0 @ sk_B)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_G)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['203', '204'])).
% 1.81/2.02  thf('206', plain, ((l1_struct_0 @ sk_D)),
% 1.81/2.02      inference('sup-', [status(thm)], ['145', '146'])).
% 1.81/2.02  thf('207', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.02      inference('sup-', [status(thm)], ['148', '149'])).
% 1.81/2.02  thf('208', plain, ((v1_funct_1 @ sk_G)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('209', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('210', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0) @ 
% 1.81/2.02           (k1_zfmisc_1 @ 
% 1.81/2.02            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (l1_struct_0 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['205', '206', '207', '208', '209'])).
% 1.81/2.02  thf('211', plain,
% 1.81/2.02      (((m1_subset_1 @ (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02         (k1_zfmisc_1 @ 
% 1.81/2.02          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02        | ~ (l1_struct_0 @ sk_C))),
% 1.81/2.02      inference('sup+', [status(thm)], ['202', '210'])).
% 1.81/2.02  thf('212', plain, ((l1_struct_0 @ sk_C)),
% 1.81/2.02      inference('sup-', [status(thm)], ['159', '160'])).
% 1.81/2.02  thf('213', plain,
% 1.81/2.02      ((m1_subset_1 @ (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['211', '212'])).
% 1.81/2.02  thf('214', plain,
% 1.81/2.02      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.81/2.02          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 1.81/2.02          | ~ (v1_funct_1 @ X18)
% 1.81/2.02          | ~ (v1_funct_1 @ X21)
% 1.81/2.02          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.81/2.02          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.81/2.02          | ((X18) = (X21))
% 1.81/2.02          | ~ (r2_funct_2 @ X19 @ X20 @ X18 @ X21))),
% 1.81/2.02      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.81/2.02  thf('215', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) @ X0)
% 1.81/2.02          | ((k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ X0)
% 1.81/2.02          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)))
% 1.81/2.02          | ~ (v1_funct_2 @ (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['213', '214'])).
% 1.81/2.02  thf('216', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_G @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('217', plain,
% 1.81/2.02      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 1.81/2.02          | ~ (v1_funct_1 @ X10)
% 1.81/2.02          | (v1_funct_1 @ (k2_partfun1 @ X11 @ X12 @ X10 @ X13)))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 1.81/2.02  thf('218', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v1_funct_1 @ 
% 1.81/2.02           (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_G @ 
% 1.81/2.02            X0))
% 1.81/2.02          | ~ (v1_funct_1 @ sk_G))),
% 1.81/2.02      inference('sup-', [status(thm)], ['216', '217'])).
% 1.81/2.02  thf('219', plain, ((v1_funct_1 @ sk_G)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('220', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (v1_funct_1 @ 
% 1.81/2.02          (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_G @ 
% 1.81/2.02           X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['218', '219'])).
% 1.81/2.02  thf('221', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_G @ 
% 1.81/2.02           X0) = (k7_relat_1 @ sk_G @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['192', '193'])).
% 1.81/2.02  thf('222', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_G @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['220', '221'])).
% 1.81/2.02  thf('223', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_G @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['200', '201'])).
% 1.81/2.02  thf('224', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_G @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('225', plain,
% 1.81/2.02      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X36 @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))))
% 1.81/2.02          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.81/2.02          | ~ (v1_funct_1 @ X36)
% 1.81/2.02          | ~ (l1_struct_0 @ X38)
% 1.81/2.02          | ~ (l1_struct_0 @ X37)
% 1.81/2.02          | ~ (l1_struct_0 @ X39)
% 1.81/2.02          | (v1_funct_2 @ (k2_tmap_1 @ X37 @ X38 @ X36 @ X39) @ 
% 1.81/2.02             (u1_struct_0 @ X39) @ (u1_struct_0 @ X38)))),
% 1.81/2.02      inference('cnf', [status(esa)], [dt_k2_tmap_1])).
% 1.81/2.02  thf('226', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0) @ 
% 1.81/2.02           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (l1_struct_0 @ X0)
% 1.81/2.02          | ~ (l1_struct_0 @ sk_D)
% 1.81/2.02          | ~ (l1_struct_0 @ sk_B)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_G)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['224', '225'])).
% 1.81/2.02  thf('227', plain, ((l1_struct_0 @ sk_D)),
% 1.81/2.02      inference('sup-', [status(thm)], ['145', '146'])).
% 1.81/2.02  thf('228', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.02      inference('sup-', [status(thm)], ['148', '149'])).
% 1.81/2.02  thf('229', plain, ((v1_funct_1 @ sk_G)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('230', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('231', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_G @ X0) @ 
% 1.81/2.02           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (l1_struct_0 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['226', '227', '228', '229', '230'])).
% 1.81/2.02  thf('232', plain,
% 1.81/2.02      (((v1_funct_2 @ (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ~ (l1_struct_0 @ sk_C))),
% 1.81/2.02      inference('sup+', [status(thm)], ['223', '231'])).
% 1.81/2.02  thf('233', plain, ((l1_struct_0 @ sk_C)),
% 1.81/2.02      inference('sup-', [status(thm)], ['159', '160'])).
% 1.81/2.02  thf('234', plain,
% 1.81/2.02      ((v1_funct_2 @ (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['232', '233'])).
% 1.81/2.02  thf('235', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) @ X0)
% 1.81/2.02          | ((k7_relat_1 @ sk_G @ (u1_struct_0 @ sk_C)) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['215', '222', '234'])).
% 1.81/2.02  thf('236', plain,
% 1.81/2.02      ((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('237', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('238', plain,
% 1.81/2.02      ((r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ sk_G)),
% 1.81/2.02      inference('demod', [status(thm)], ['236', '237'])).
% 1.81/2.02  thf('239', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_E @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('demod', [status(thm)], ['7', '8'])).
% 1.81/2.02  thf(redefinition_r1_funct_2, axiom,
% 1.81/2.02    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.81/2.02     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 1.81/2.02         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 1.81/2.02         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.81/2.02         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 1.81/2.02         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.81/2.02       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 1.81/2.02  thf('240', plain,
% 1.81/2.02      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.81/2.02          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 1.81/2.02          | ~ (v1_funct_1 @ X26)
% 1.81/2.02          | (v1_xboole_0 @ X29)
% 1.81/2.02          | (v1_xboole_0 @ X28)
% 1.81/2.02          | ~ (v1_funct_1 @ X30)
% 1.81/2.02          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 1.81/2.02          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 1.81/2.02          | ((X26) = (X30))
% 1.81/2.02          | ~ (r1_funct_2 @ X27 @ X28 @ X31 @ X29 @ X26 @ X30))),
% 1.81/2.02      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 1.81/2.02  thf('241', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.81/2.02         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.81/2.02             X1 @ sk_E @ X0)
% 1.81/2.02          | ((sk_E) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.81/2.02          | ~ (v1_funct_1 @ X0)
% 1.81/2.02          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | (v1_xboole_0 @ X1)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_E)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['239', '240'])).
% 1.81/2.02  thf('242', plain, ((v1_funct_1 @ sk_E)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('243', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['19', '20'])).
% 1.81/2.02  thf('244', plain,
% 1.81/2.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.81/2.02         (~ (r1_funct_2 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ X2 @ 
% 1.81/2.02             X1 @ sk_E @ X0)
% 1.81/2.02          | ((sk_E) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 1.81/2.02          | ~ (v1_funct_1 @ X0)
% 1.81/2.02          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | (v1_xboole_0 @ X1))),
% 1.81/2.02      inference('demod', [status(thm)], ['241', '242', '243'])).
% 1.81/2.02  thf('245', plain,
% 1.81/2.02      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ~ (v1_funct_1 @ sk_G)
% 1.81/2.02        | ~ (v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ~ (m1_subset_1 @ sk_G @ 
% 1.81/2.02             (k1_zfmisc_1 @ 
% 1.81/2.02              (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02        | ((sk_E) = (sk_G)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['238', '244'])).
% 1.81/2.02  thf('246', plain, ((v1_funct_1 @ sk_G)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('247', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_G @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('248', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_G @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('249', plain,
% 1.81/2.02      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ((sk_E) = (sk_G)))),
% 1.81/2.02      inference('demod', [status(thm)], ['245', '246', '247', '248'])).
% 1.81/2.02  thf('250', plain,
% 1.81/2.02      ((((sk_E) = (sk_G)) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('simplify', [status(thm)], ['249'])).
% 1.81/2.02  thf(fc2_struct_0, axiom,
% 1.81/2.02    (![A:$i]:
% 1.81/2.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.81/2.02       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.81/2.02  thf('251', plain,
% 1.81/2.02      (![X25 : $i]:
% 1.81/2.02         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 1.81/2.02          | ~ (l1_struct_0 @ X25)
% 1.81/2.02          | (v2_struct_0 @ X25))),
% 1.81/2.02      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.81/2.02  thf('252', plain,
% 1.81/2.02      ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 1.81/2.02      inference('sup-', [status(thm)], ['250', '251'])).
% 1.81/2.02  thf('253', plain, ((l1_struct_0 @ sk_B)),
% 1.81/2.02      inference('sup-', [status(thm)], ['148', '149'])).
% 1.81/2.02  thf('254', plain, ((((sk_E) = (sk_G)) | (v2_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['252', '253'])).
% 1.81/2.02  thf('255', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('256', plain, (((sk_E) = (sk_G))),
% 1.81/2.02      inference('clc', [status(thm)], ['254', '255'])).
% 1.81/2.02  thf('257', plain, (((sk_E) = (sk_G))),
% 1.81/2.02      inference('clc', [status(thm)], ['254', '255'])).
% 1.81/2.02  thf('258', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ X0)
% 1.81/2.02          | ((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['235', '256', '257'])).
% 1.81/2.02  thf('259', plain,
% 1.81/2.02      (((~ (v1_funct_1 @ sk_F)
% 1.81/2.02         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02         | ~ (m1_subset_1 @ sk_F @ 
% 1.81/2.02              (k1_zfmisc_1 @ 
% 1.81/2.02               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02         | ((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F))))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['181', '258'])).
% 1.81/2.02  thf('260', plain, ((v1_funct_1 @ sk_F)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('261', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('262', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_F @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('263', plain,
% 1.81/2.02      ((((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F)))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 1.81/2.02  thf('264', plain,
% 1.81/2.02      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)
% 1.81/2.02        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('265', plain,
% 1.81/2.02      (~
% 1.81/2.02       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)) | 
% 1.81/2.02       ~
% 1.81/2.02       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.81/2.02      inference('split', [status(esa)], ['264'])).
% 1.81/2.02  thf('266', plain, (((sk_E) = (sk_G))),
% 1.81/2.02      inference('clc', [status(thm)], ['254', '255'])).
% 1.81/2.02  thf('267', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('split', [status(esa)], ['177'])).
% 1.81/2.02  thf('268', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('269', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['267', '268'])).
% 1.81/2.02  thf('270', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('sup+', [status(thm)], ['266', '269'])).
% 1.81/2.02  thf('271', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ X0)
% 1.81/2.02          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['93', '112', '131'])).
% 1.81/2.02  thf('272', plain,
% 1.81/2.02      (((~ (v1_funct_1 @ sk_F)
% 1.81/2.02         | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02         | ~ (m1_subset_1 @ sk_F @ 
% 1.81/2.02              (k1_zfmisc_1 @ 
% 1.81/2.02               (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02         | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F))))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['270', '271'])).
% 1.81/2.02  thf('273', plain, ((v1_funct_1 @ sk_F)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('274', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('275', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_F @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('276', plain,
% 1.81/2.02      ((((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F)))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['272', '273', '274', '275'])).
% 1.81/2.02  thf('277', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B)
% 1.81/2.02        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ 
% 1.81/2.02           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | (v2_struct_0 @ sk_C)
% 1.81/2.02        | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('simplify', [status(thm)], ['71'])).
% 1.81/2.02  thf('278', plain,
% 1.81/2.02      ((((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02          (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02         | (v2_struct_0 @ sk_D)
% 1.81/2.02         | (v2_struct_0 @ sk_C)
% 1.81/2.02         | (v2_struct_0 @ sk_B)))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('sup+', [status(thm)], ['276', '277'])).
% 1.81/2.02  thf('279', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         ((m1_subset_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ 
% 1.81/2.02           (k1_zfmisc_1 @ 
% 1.81/2.02            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (l1_struct_0 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['166', '167', '168', '169', '170'])).
% 1.81/2.02  thf('280', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_F @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('281', plain,
% 1.81/2.02      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.81/2.02          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 1.81/2.02          | ~ (v1_funct_1 @ X18)
% 1.81/2.02          | ~ (v1_funct_1 @ X21)
% 1.81/2.02          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.81/2.02          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.81/2.02          | ((X18) = (X21))
% 1.81/2.02          | ~ (r2_funct_2 @ X19 @ X20 @ X18 @ X21))),
% 1.81/2.02      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.81/2.02  thf('282', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02             X0)
% 1.81/2.02          | ((sk_F) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ X0)
% 1.81/2.02          | ~ (v1_funct_1 @ sk_F)
% 1.81/2.02          | ~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['280', '281'])).
% 1.81/2.02  thf('283', plain, ((v1_funct_1 @ sk_F)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('284', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('285', plain,
% 1.81/2.02      (![X0 : $i]:
% 1.81/2.02         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02             X0)
% 1.81/2.02          | ((sk_F) = (X0))
% 1.81/2.02          | ~ (m1_subset_1 @ X0 @ 
% 1.81/2.02               (k1_zfmisc_1 @ 
% 1.81/2.02                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 1.81/2.02          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02          | ~ (v1_funct_1 @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['282', '283', '284'])).
% 1.81/2.02  thf('286', plain,
% 1.81/2.02      ((~ (l1_struct_0 @ sk_C)
% 1.81/2.02        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.81/2.02        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ 
% 1.81/2.02             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ((sk_F) = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 1.81/2.02        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['279', '285'])).
% 1.81/2.02  thf('287', plain, ((l1_struct_0 @ sk_C)),
% 1.81/2.02      inference('sup-', [status(thm)], ['159', '160'])).
% 1.81/2.02  thf('288', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('289', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 1.81/2.02      inference('demod', [status(thm)], ['138', '139'])).
% 1.81/2.02  thf('290', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('291', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('292', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('293', plain,
% 1.81/2.02      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.81/2.02      inference('demod', [status(thm)],
% 1.81/2.02                ['286', '287', '288', '289', '290', '291', '292'])).
% 1.81/2.02  thf('294', plain,
% 1.81/2.02      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ 
% 1.81/2.02        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('demod', [status(thm)], ['154', '161'])).
% 1.81/2.02  thf('295', plain,
% 1.81/2.02      ((((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))
% 1.81/2.02        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02             (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C))))),
% 1.81/2.02      inference('demod', [status(thm)], ['293', '294'])).
% 1.81/2.02  thf('296', plain,
% 1.81/2.02      ((((v2_struct_0 @ sk_B)
% 1.81/2.02         | (v2_struct_0 @ sk_C)
% 1.81/2.02         | (v2_struct_0 @ sk_D)
% 1.81/2.02         | ((sk_F) = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))))
% 1.81/2.02         <= (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['278', '295'])).
% 1.81/2.02  thf('297', plain,
% 1.81/2.02      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 1.81/2.02         = (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)))),
% 1.81/2.02      inference('clc', [status(thm)], ['44', '45'])).
% 1.81/2.02  thf('298', plain,
% 1.81/2.02      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.81/2.02      inference('split', [status(esa)], ['264'])).
% 1.81/2.02  thf('299', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('300', plain,
% 1.81/2.02      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['298', '299'])).
% 1.81/2.02  thf('301', plain,
% 1.81/2.02      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) @ sk_F))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['297', '300'])).
% 1.81/2.02  thf('302', plain,
% 1.81/2.02      (((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02            sk_F)
% 1.81/2.02         | (v2_struct_0 @ sk_D)
% 1.81/2.02         | (v2_struct_0 @ sk_C)
% 1.81/2.02         | (v2_struct_0 @ sk_B)))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('sup-', [status(thm)], ['296', '301'])).
% 1.81/2.02  thf('303', plain,
% 1.81/2.02      ((m1_subset_1 @ sk_F @ 
% 1.81/2.02        (k1_zfmisc_1 @ 
% 1.81/2.02         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('304', plain,
% 1.81/2.02      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.81/2.02         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.81/2.02          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 1.81/2.02          | ~ (v1_funct_1 @ X18)
% 1.81/2.02          | ~ (v1_funct_1 @ X21)
% 1.81/2.02          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.81/2.02          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.81/2.02          | (r2_funct_2 @ X19 @ X20 @ X18 @ X21)
% 1.81/2.02          | ((X18) != (X21)))),
% 1.81/2.02      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 1.81/2.02  thf('305', plain,
% 1.81/2.02      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.81/2.02         ((r2_funct_2 @ X19 @ X20 @ X21 @ X21)
% 1.81/2.02          | ~ (v1_funct_1 @ X21)
% 1.81/2.02          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.81/2.02          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.81/2.02      inference('simplify', [status(thm)], ['304'])).
% 1.81/2.02  thf('306', plain,
% 1.81/2.02      ((~ (v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.81/2.02        | ~ (v1_funct_1 @ sk_F)
% 1.81/2.02        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02           sk_F))),
% 1.81/2.02      inference('sup-', [status(thm)], ['303', '305'])).
% 1.81/2.02  thf('307', plain,
% 1.81/2.02      ((v1_funct_2 @ sk_F @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('308', plain, ((v1_funct_1 @ sk_F)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('309', plain,
% 1.81/2.02      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ sk_F)),
% 1.81/2.02      inference('demod', [status(thm)], ['306', '307', '308'])).
% 1.81/2.02  thf('310', plain,
% 1.81/2.02      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B)))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['302', '309'])).
% 1.81/2.02  thf('311', plain, (~ (v2_struct_0 @ sk_D)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('312', plain,
% 1.81/2.02      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C)))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('clc', [status(thm)], ['310', '311'])).
% 1.81/2.02  thf('313', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('314', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_C))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) & 
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('clc', [status(thm)], ['312', '313'])).
% 1.81/2.02  thf('315', plain, (~ (v2_struct_0 @ sk_C)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('316', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 1.81/2.02       ~
% 1.81/2.02       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.81/2.02      inference('sup-', [status(thm)], ['314', '315'])).
% 1.81/2.02  thf('317', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F)) | 
% 1.81/2.02       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.81/2.02      inference('split', [status(esa)], ['177'])).
% 1.81/2.02  thf('318', plain,
% 1.81/2.02      (((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 1.81/2.02      inference('sat_resolution*', [status(thm)], ['265', '316', '317'])).
% 1.81/2.02  thf('319', plain, (((k7_relat_1 @ sk_E @ (u1_struct_0 @ sk_C)) = (sk_F))),
% 1.81/2.02      inference('simpl_trail', [status(thm)], ['263', '318'])).
% 1.81/2.02  thf('320', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_D)
% 1.81/2.02        | (v2_struct_0 @ sk_C)
% 1.81/2.02        | (v2_struct_0 @ sk_B)
% 1.81/2.02        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) = (sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['175', '319'])).
% 1.81/2.02  thf('321', plain,
% 1.81/2.02      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('split', [status(esa)], ['264'])).
% 1.81/2.02  thf('322', plain, (((sk_D) = (sk_A))),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('323', plain,
% 1.81/2.02      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['321', '322'])).
% 1.81/2.02  thf('324', plain, (((sk_E) = (sk_G))),
% 1.81/2.02      inference('clc', [status(thm)], ['254', '255'])).
% 1.81/2.02  thf('325', plain,
% 1.81/2.02      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))
% 1.81/2.02         <= (~
% 1.81/2.02             ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02               (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F)))),
% 1.81/2.02      inference('demod', [status(thm)], ['323', '324'])).
% 1.81/2.02  thf('326', plain,
% 1.81/2.02      (~
% 1.81/2.02       ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02         (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_G) @ sk_F))),
% 1.81/2.02      inference('sat_resolution*', [status(thm)], ['265', '316'])).
% 1.81/2.02  thf('327', plain,
% 1.81/2.02      (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 1.81/2.02          (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F)),
% 1.81/2.02      inference('simpl_trail', [status(thm)], ['325', '326'])).
% 1.81/2.02  thf('328', plain,
% 1.81/2.02      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ 
% 1.81/2.02           sk_F)
% 1.81/2.02        | (v2_struct_0 @ sk_B)
% 1.81/2.02        | (v2_struct_0 @ sk_C)
% 1.81/2.02        | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('sup-', [status(thm)], ['320', '327'])).
% 1.81/2.02  thf('329', plain,
% 1.81/2.02      ((r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_F @ sk_F)),
% 1.81/2.02      inference('demod', [status(thm)], ['306', '307', '308'])).
% 1.81/2.02  thf('330', plain,
% 1.81/2.02      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 1.81/2.02      inference('demod', [status(thm)], ['328', '329'])).
% 1.81/2.02  thf('331', plain, (~ (v2_struct_0 @ sk_B)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('332', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 1.81/2.02      inference('clc', [status(thm)], ['330', '331'])).
% 1.81/2.02  thf('333', plain, (~ (v2_struct_0 @ sk_D)),
% 1.81/2.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.02  thf('334', plain, ((v2_struct_0 @ sk_C)),
% 1.81/2.02      inference('clc', [status(thm)], ['332', '333'])).
% 1.81/2.02  thf('335', plain, ($false), inference('demod', [status(thm)], ['0', '334'])).
% 1.81/2.02  
% 1.81/2.02  % SZS output end Refutation
% 1.81/2.02  
% 1.81/2.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
