%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ucS71Bp6W6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  172 (1629 expanded)
%              Number of leaves         :   46 ( 500 expanded)
%              Depth                    :   27
%              Number of atoms          : 1477 (38736 expanded)
%              Number of equality atoms :   49 ( 755 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(t60_tmap_1,conjecture,(
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
                 => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                   => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) )).

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
                   => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('20',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

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

thf('27',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ( r1_funct_2 @ X32 @ X33 @ X36 @ X34 @ X31 @ X35 )
      | ( X31 != X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r1_funct_2 @ X32 @ X33 @ X36 @ X34 @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X34 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('37',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('41',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('53',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('55',plain,(
    ! [X43: $i] :
      ( ( m1_pre_topc @ X43 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( m1_pre_topc @ X30 @ ( g1_pre_topc @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['54','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('64',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) )
      | ( m1_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('68',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k1_relat_1 @ sk_D ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['69','70'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('78',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','80'])).

thf('82',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

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

thf('86',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ( ( k2_tmap_1 @ X39 @ X37 @ X40 @ X38 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) @ X40 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','24'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('97',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k2_partfun1 @ X20 @ X21 @ X19 @ X22 )
        = ( k7_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95','100','101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','80'])).

thf('106',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('107',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( ( k7_relat_1 @ X6 @ X7 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['10','11'])).

thf('110',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','80'])).

thf('112',plain,
    ( ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['82','117'])).

thf('119',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','118'])).

thf('120',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('123',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['0','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ucS71Bp6W6
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 164 iterations in 0.047s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.49  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.22/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.49  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(t60_tmap_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.49             ( l1_pre_topc @ B ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.49               ( ![D:$i]:
% 0.22/0.49                 ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.49                     ( v1_funct_2 @
% 0.22/0.49                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.49                     ( m1_subset_1 @
% 0.22/0.49                       D @ 
% 0.22/0.49                       ( k1_zfmisc_1 @
% 0.22/0.49                         ( k2_zfmisc_1 @
% 0.22/0.49                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.49                   ( ( ( g1_pre_topc @
% 0.22/0.49                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.49                       ( g1_pre_topc @
% 0.22/0.49                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.49                     ( r1_funct_2 @
% 0.22/0.49                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.49                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.22/0.49                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.49            ( l1_pre_topc @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.49                ( l1_pre_topc @ B ) ) =>
% 0.22/0.49              ( ![C:$i]:
% 0.22/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.49                  ( ![D:$i]:
% 0.22/0.49                    ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.49                        ( v1_funct_2 @
% 0.22/0.49                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.49                        ( m1_subset_1 @
% 0.22/0.49                          D @ 
% 0.22/0.49                          ( k1_zfmisc_1 @
% 0.22/0.49                            ( k2_zfmisc_1 @
% 0.22/0.49                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.49                      ( ( ( g1_pre_topc @
% 0.22/0.49                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.49                          ( g1_pre_topc @
% 0.22/0.49                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.49                        ( r1_funct_2 @
% 0.22/0.49                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.49                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.22/0.49                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.22/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(cc5_funct_2, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.49             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.22/0.49          | (v1_partfun1 @ X14 @ X15)
% 0.22/0.49          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.22/0.49          | ~ (v1_funct_1 @ X14)
% 0.22/0.49          | (v1_xboole_0 @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (v1_funct_1 @ sk_D)
% 0.22/0.49        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.49  thf(d4_partfun1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.49       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X17 : $i, X18 : $i]:
% 0.22/0.49         (~ (v1_partfun1 @ X18 @ X17)
% 0.22/0.49          | ((k1_relat_1 @ X18) = (X17))
% 0.22/0.49          | ~ (v4_relat_1 @ X18 @ X17)
% 0.22/0.49          | ~ (v1_relat_1 @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_D)
% 0.22/0.49        | ~ (v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.22/0.49        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(cc1_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( v1_relat_1 @ C ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.49         ((v1_relat_1 @ X8)
% 0.22/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.49  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(cc2_relset_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.49         ((v4_relat_1 @ X11 @ X12)
% 0.22/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.49  thf('15', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.22/0.49  thf(fc2_struct_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X26 : $i]:
% 0.22/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.22/0.49          | ~ (l1_struct_0 @ X26)
% 0.22/0.49          | (v2_struct_0 @ X26))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))
% 0.22/0.49        | (v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_l1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['18', '21'])).
% 0.22/0.49  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '24'])).
% 0.22/0.49  thf(redefinition_r1_funct_2, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.49     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.22/0.49         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.22/0.49         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.49         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.22/0.49         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.22/0.49       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.22/0.49          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.22/0.49          | ~ (v1_funct_1 @ X31)
% 0.22/0.49          | (v1_xboole_0 @ X34)
% 0.22/0.49          | (v1_xboole_0 @ X33)
% 0.22/0.49          | ~ (v1_funct_1 @ X35)
% 0.22/0.49          | ~ (v1_funct_2 @ X35 @ X36 @ X34)
% 0.22/0.49          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.22/0.49          | (r1_funct_2 @ X32 @ X33 @ X36 @ X34 @ X31 @ X35)
% 0.22/0.49          | ((X31) != (X35)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.49         ((r1_funct_2 @ X32 @ X33 @ X36 @ X34 @ X35 @ X35)
% 0.22/0.49          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.22/0.49          | ~ (v1_funct_2 @ X35 @ X36 @ X34)
% 0.22/0.49          | (v1_xboole_0 @ X33)
% 0.22/0.49          | (v1_xboole_0 @ X34)
% 0.22/0.49          | ~ (v1_funct_1 @ X35)
% 0.22/0.49          | ~ (v1_funct_2 @ X35 @ X32 @ X33)
% 0.22/0.49          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.49          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.22/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49          | (v1_xboole_0 @ X0)
% 0.22/0.49          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.49          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.22/0.49             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '28'])).
% 0.22/0.49  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.49          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.22/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49          | (v1_xboole_0 @ X0)
% 0.22/0.49          | (r1_funct_2 @ X1 @ X0 @ (k1_relat_1 @ sk_D) @ 
% 0.22/0.49             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.22/0.49      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['25', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.22/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.49          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('40', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.49          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.49  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t1_tsep_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( m1_subset_1 @
% 0.22/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X41 : $i, X42 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X41 @ X42)
% 0.22/0.49          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.22/0.49          | ~ (l1_pre_topc @ X42))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.49  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.49  thf(t3_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('48', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i]:
% 0.22/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.22/0.49        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.49  thf('51', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('52', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.22/0.49        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.22/0.49  thf('54', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf(t2_tsep_1, axiom,
% 0.22/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      (![X43 : $i]: ((m1_pre_topc @ X43 @ X43) | ~ (l1_pre_topc @ X43))),
% 0.22/0.49      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.49  thf(t65_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_pre_topc @ B ) =>
% 0.22/0.49           ( ( m1_pre_topc @ A @ B ) <=>
% 0.22/0.49             ( m1_pre_topc @
% 0.22/0.49               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      (![X29 : $i, X30 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X29)
% 0.22/0.49          | ~ (m1_pre_topc @ X30 @ X29)
% 0.22/0.49          | (m1_pre_topc @ X30 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X29) @ (u1_pre_topc @ X29)))
% 0.22/0.49          | ~ (l1_pre_topc @ X30))),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | (m1_pre_topc @ X0 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.49  thf('58', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((m1_pre_topc @ X0 @ 
% 0.22/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['57'])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (((m1_pre_topc @ sk_B @ 
% 0.22/0.49         (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.49      inference('sup+', [status(thm)], ['54', '58'])).
% 0.22/0.49  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      ((m1_pre_topc @ sk_B @ 
% 0.22/0.49        (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('63', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.49         = (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['62', '63'])).
% 0.22/0.49  thf(t59_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @
% 0.22/0.49             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.22/0.49           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.22/0.49  thf('65', plain,
% 0.22/0.49      (![X27 : $i, X28 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X27 @ 
% 0.22/0.49             (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))
% 0.22/0.49          | (m1_pre_topc @ X27 @ X28)
% 0.22/0.49          | ~ (l1_pre_topc @ X28))),
% 0.22/0.49      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X0 @ 
% 0.22/0.49             (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49          | ~ (l1_pre_topc @ sk_C)
% 0.22/0.49          | (m1_pre_topc @ X0 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.49  thf('67', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_m1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.49  thf('68', plain,
% 0.22/0.49      (![X24 : $i, X25 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X24 @ X25)
% 0.22/0.49          | (l1_pre_topc @ X24)
% 0.22/0.49          | ~ (l1_pre_topc @ X25))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.49  thf('69', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.49  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('71', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.49      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.49  thf('72', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X0 @ 
% 0.22/0.49             (g1_pre_topc @ (k1_relat_1 @ sk_D) @ (u1_pre_topc @ sk_B)))
% 0.22/0.49          | (m1_pre_topc @ X0 @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['66', '71'])).
% 0.22/0.49  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['61', '72'])).
% 0.22/0.49  thf('74', plain,
% 0.22/0.49      (![X41 : $i, X42 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X41 @ X42)
% 0.22/0.49          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.22/0.49          | ~ (l1_pre_topc @ X42))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.49  thf('75', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_C)
% 0.22/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.49  thf('76', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.49      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.49  thf('77', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('78', plain,
% 0.22/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_D) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.49      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.22/0.49  thf('79', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('80', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.49  thf('81', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['53', '80'])).
% 0.22/0.49  thf('82', plain,
% 0.22/0.49      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.49          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['41', '81'])).
% 0.22/0.49  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('84', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '24'])).
% 0.22/0.49  thf('85', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf(d4_tmap_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.49             ( l1_pre_topc @ B ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.49                 ( m1_subset_1 @
% 0.22/0.49                   C @ 
% 0.22/0.49                   ( k1_zfmisc_1 @
% 0.22/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.49               ( ![D:$i]:
% 0.22/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.49                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.22/0.49                     ( k2_partfun1 @
% 0.22/0.49                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.49                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('86', plain,
% 0.22/0.49      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.22/0.49         ((v2_struct_0 @ X37)
% 0.22/0.49          | ~ (v2_pre_topc @ X37)
% 0.22/0.49          | ~ (l1_pre_topc @ X37)
% 0.22/0.49          | ~ (m1_pre_topc @ X38 @ X39)
% 0.22/0.49          | ((k2_tmap_1 @ X39 @ X37 @ X40 @ X38)
% 0.22/0.49              = (k2_partfun1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37) @ 
% 0.22/0.49                 X40 @ (u1_struct_0 @ X38)))
% 0.22/0.49          | ~ (m1_subset_1 @ X40 @ 
% 0.22/0.49               (k1_zfmisc_1 @ 
% 0.22/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 0.22/0.49          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 0.22/0.49          | ~ (v1_funct_1 @ X40)
% 0.22/0.49          | ~ (l1_pre_topc @ X39)
% 0.22/0.49          | ~ (v2_pre_topc @ X39)
% 0.22/0.49          | (v2_struct_0 @ X39))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.49  thf('87', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X1 @ 
% 0.22/0.49             (k1_zfmisc_1 @ 
% 0.22/0.49              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.22/0.49          | (v2_struct_0 @ sk_B)
% 0.22/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.49          | ~ (v1_funct_1 @ X1)
% 0.22/0.49          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.22/0.49          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.22/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.22/0.49                 X1 @ (u1_struct_0 @ X2)))
% 0.22/0.49          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (v2_pre_topc @ X0)
% 0.22/0.49          | (v2_struct_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['85', '86'])).
% 0.22/0.49  thf('88', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('90', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('91', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('92', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X1 @ 
% 0.22/0.49             (k1_zfmisc_1 @ 
% 0.22/0.49              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.22/0.49          | (v2_struct_0 @ sk_B)
% 0.22/0.49          | ~ (v1_funct_1 @ X1)
% 0.22/0.49          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.22/0.49          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.22/0.49              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.22/0.49                 (u1_struct_0 @ X2)))
% 0.22/0.49          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.22/0.49          | ~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (v2_pre_topc @ X0)
% 0.22/0.49          | (v2_struct_0 @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 0.22/0.49  thf('93', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ sk_A)
% 0.22/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.49          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.49              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49                 sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.49          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.49          | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['84', '92'])).
% 0.22/0.49  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('96', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_D @ 
% 0.22/0.49        (k1_zfmisc_1 @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('demod', [status(thm)], ['1', '24'])).
% 0.22/0.49  thf(redefinition_k2_partfun1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.49       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.22/0.49  thf('97', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.22/0.49          | ~ (v1_funct_1 @ X19)
% 0.22/0.49          | ((k2_partfun1 @ X20 @ X21 @ X19 @ X22) = (k7_relat_1 @ X19 @ X22)))),
% 0.22/0.49      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.22/0.49  thf('98', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.49            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.22/0.49          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['96', '97'])).
% 0.22/0.49  thf('99', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('100', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ X0)
% 0.22/0.49           = (k7_relat_1 @ sk_D @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['98', '99'])).
% 0.22/0.49  thf('101', plain,
% 0.22/0.49      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('103', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((v2_struct_0 @ sk_A)
% 0.22/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.49          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.49              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.49          | (v2_struct_0 @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['93', '94', '95', '100', '101', '102'])).
% 0.22/0.49  thf('104', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_B)
% 0.22/0.49        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.49            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['83', '103'])).
% 0.22/0.49  thf('105', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['53', '80'])).
% 0.22/0.49  thf('106', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.49  thf(t97_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.49         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.49  thf('107', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.22/0.49          | ((k7_relat_1 @ X6 @ X7) = (X6))
% 0.22/0.49          | ~ (v1_relat_1 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.49  thf('108', plain,
% 0.22/0.49      ((~ (v1_relat_1 @ sk_D)
% 0.22/0.49        | ((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['106', '107'])).
% 0.22/0.49  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('110', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.22/0.49      inference('demod', [status(thm)], ['108', '109'])).
% 0.22/0.49  thf('111', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['53', '80'])).
% 0.22/0.49  thf('112', plain, (((k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (sk_D))),
% 0.22/0.49      inference('demod', [status(thm)], ['110', '111'])).
% 0.22/0.49  thf('113', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_B)
% 0.22/0.49        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['104', '105', '112'])).
% 0.22/0.49  thf('114', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('115', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.22/0.49      inference('clc', [status(thm)], ['113', '114'])).
% 0.22/0.49  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('117', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.22/0.49      inference('clc', [status(thm)], ['115', '116'])).
% 0.22/0.49  thf('118', plain,
% 0.22/0.49      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.22/0.49      inference('demod', [status(thm)], ['82', '117'])).
% 0.22/0.49  thf('119', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['38', '118'])).
% 0.22/0.49  thf('120', plain,
% 0.22/0.49      (![X26 : $i]:
% 0.22/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.22/0.49          | ~ (l1_struct_0 @ X26)
% 0.22/0.49          | (v2_struct_0 @ X26))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.49  thf('121', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['119', '120'])).
% 0.22/0.49  thf('122', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('123', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['121', '122'])).
% 0.22/0.49  thf('124', plain, ($false), inference('demod', [status(thm)], ['0', '123'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
