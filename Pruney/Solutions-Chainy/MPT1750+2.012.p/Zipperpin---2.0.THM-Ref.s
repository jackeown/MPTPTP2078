%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zM6EF3LcZb

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  156 (2953 expanded)
%              Number of leaves         :   42 ( 827 expanded)
%              Depth                    :   34
%              Number of atoms          : 1397 (70135 expanded)
%              Number of equality atoms :   63 (2839 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('2',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X21 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( g1_pre_topc @ X25 @ X26 )
       != ( g1_pre_topc @ X23 @ X24 ) )
      | ( X26 = X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('10',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X21 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('11',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( ( g1_pre_topc @ X25 @ X26 )
       != ( g1_pre_topc @ X23 @ X24 ) )
      | ( X25 = X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('18',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','20'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('28',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25','28'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('39',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','34','39'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('41',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('44',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','48'])).

thf(reflexivity_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ) )).

thf('51',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r1_funct_2 @ X27 @ X28 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['52','53','56'])).

thf('58',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('61',plain,
    ( ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['61'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( ( k7_relat_1 @ X3 @ X4 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('69',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('72',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','48'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('76',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','76'])).

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

thf('78',plain,(
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

thf('79',plain,(
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
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('84',plain,(
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
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
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
    inference('sup-',[status(thm)],['74','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','48'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('89',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k2_partfun1 @ X17 @ X18 @ X16 @ X19 )
        = ( k7_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('94',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','86','87','92','93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','95'])).

thf('97',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['72','102'])).

thf('104',plain,
    ( ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['32','33'])).

thf('106',plain,(
    ~ ( r1_funct_2 @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','106'])).

thf('108',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('111',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    $false ),
    inference(demod,[status(thm)],['0','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zM6EF3LcZb
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:33:27 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 99 iterations in 0.047s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.22/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(t60_tmap_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52             ( l1_pre_topc @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.52                     ( v1_funct_2 @
% 0.22/0.52                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52                     ( m1_subset_1 @
% 0.22/0.52                       D @ 
% 0.22/0.52                       ( k1_zfmisc_1 @
% 0.22/0.52                         ( k2_zfmisc_1 @
% 0.22/0.52                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52                   ( ( ( g1_pre_topc @
% 0.22/0.52                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.52                       ( g1_pre_topc @
% 0.22/0.52                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.52                     ( r1_funct_2 @
% 0.22/0.52                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.52                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.22/0.52                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52            ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.52                ( l1_pre_topc @ B ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.52                  ( ![D:$i]:
% 0.22/0.52                    ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.52                        ( v1_funct_2 @
% 0.22/0.52                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.52                        ( m1_subset_1 @
% 0.22/0.52                          D @ 
% 0.22/0.52                          ( k1_zfmisc_1 @
% 0.22/0.52                            ( k2_zfmisc_1 @
% 0.22/0.52                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.52                      ( ( ( g1_pre_topc @
% 0.22/0.52                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.52                          ( g1_pre_topc @
% 0.22/0.52                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.52                        ( r1_funct_2 @
% 0.22/0.52                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.52                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.22/0.52                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.22/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_u1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( m1_subset_1 @
% 0.22/0.52         ( u1_pre_topc @ A ) @ 
% 0.22/0.52         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X21 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (u1_pre_topc @ X21) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.22/0.52          | ~ (l1_pre_topc @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.22/0.52  thf(free_g1_pre_topc, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ![C:$i,D:$i]:
% 0.22/0.52         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.22/0.52           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.52         (((g1_pre_topc @ X25 @ X26) != (g1_pre_topc @ X23 @ X24))
% 0.22/0.52          | ((X26) = (X24))
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.22/0.52      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X0)
% 0.22/0.52          | ((u1_pre_topc @ X0) = (X1))
% 0.22/0.52          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.52              != (g1_pre_topc @ X2 @ X1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.52            != (g1_pre_topc @ X1 @ X0))
% 0.22/0.52          | ((u1_pre_topc @ sk_B) = (X0))
% 0.22/0.52          | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.52  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.52            != (g1_pre_topc @ X1 @ X0))
% 0.22/0.52          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X21 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (u1_pre_topc @ X21) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21))))
% 0.22/0.52          | ~ (l1_pre_topc @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.22/0.52         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.22/0.52        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.52         (((g1_pre_topc @ X25 @ X26) != (g1_pre_topc @ X23 @ X24))
% 0.22/0.52          | ((X25) = (X23))
% 0.22/0.52          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.22/0.52      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((u1_struct_0 @ sk_B) = (X0))
% 0.22/0.52          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C))
% 0.22/0.52              != (g1_pre_topc @ X0 @ X1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('17', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((u1_struct_0 @ sk_B) = (X0))
% 0.22/0.52          | ((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.52              != (g1_pre_topc @ X0 @ X1)))),
% 0.22/0.52      inference('demod', [status(thm)], ['15', '18'])).
% 0.22/0.52  thf('20', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '20'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '20'])).
% 0.22/0.52  thf(cc5_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.52             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.22/0.52          | (v1_partfun1 @ X11 @ X12)
% 0.22/0.52          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.22/0.52          | ~ (v1_funct_1 @ X11)
% 0.22/0.52          | (v1_xboole_0 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (v1_funct_1 @ sk_D)
% 0.22/0.52        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('27', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['19'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v1_partfun1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['24', '25', '28'])).
% 0.22/0.52  thf(d4_partfun1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.52       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         (~ (v1_partfun1 @ X15 @ X14)
% 0.22/0.52          | ((k1_relat_1 @ X15) = (X14))
% 0.22/0.52          | ~ (v4_relat_1 @ X15 @ X14)
% 0.22/0.52          | ~ (v1_relat_1 @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_D)
% 0.22/0.52        | ~ (v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.22/0.52        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( v1_relat_1 @ C ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.52         ((v1_relat_1 @ X5)
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.52  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         ((v4_relat_1 @ X8 @ X9)
% 0.22/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.52  thf('37', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['19'])).
% 0.22/0.52  thf('39', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '34', '39'])).
% 0.22/0.52  thf(fc2_struct_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X22 : $i]:
% 0.22/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.22/0.52          | ~ (l1_struct_0 @ X22)
% 0.22/0.52          | (v2_struct_0 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))
% 0.22/0.52        | (v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_l1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.52  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      ((((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '45'])).
% 0.22/0.52  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('48', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['21', '48'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['21', '48'])).
% 0.22/0.52  thf(reflexivity_r1_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.52     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.22/0.52         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.22/0.52         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.52         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.22/0.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.22/0.52       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.52         ((r1_funct_2 @ X27 @ X28 @ X29 @ X30 @ X31 @ X31)
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.22/0.52          | ~ (v1_funct_2 @ X31 @ X27 @ X28)
% 0.22/0.52          | ~ (v1_funct_1 @ X31)
% 0.22/0.52          | (v1_xboole_0 @ X30)
% 0.22/0.52          | (v1_xboole_0 @ X28)
% 0.22/0.52          | ~ (v1_funct_1 @ X32)
% 0.22/0.52          | ~ (v1_funct_2 @ X32 @ X29 @ X30)
% 0.22/0.52          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.22/0.52      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.52          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X2)
% 0.22/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (v1_xboole_0 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.22/0.52             X0 @ sk_D @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.52  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('55', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.52          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.22/0.52          | ~ (v1_funct_1 @ X2)
% 0.22/0.52          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | (v1_xboole_0 @ X0)
% 0.22/0.52          | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.22/0.52             X0 @ sk_D @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['52', '53', '56'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | ~ (v1_funct_1 @ sk_D)
% 0.22/0.52        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['49', '57'])).
% 0.22/0.52  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (((r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52         (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.52        | (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.22/0.52      inference('simplify', [status(thm)], ['61'])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['63'])).
% 0.22/0.52  thf(t97_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ B ) =>
% 0.22/0.52       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.52         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (![X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.22/0.52          | ((k7_relat_1 @ X3 @ X4) = (X3))
% 0.22/0.52          | ~ (v1_relat_1 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('68', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['19'])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.22/0.52  thf('70', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('71', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('72', plain,
% 0.22/0.52      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.22/0.52  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['21', '48'])).
% 0.22/0.52  thf('75', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['19'])).
% 0.22/0.52  thf('76', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('77', plain, (((u1_struct_0 @ sk_B) = (k1_relat_1 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['75', '76'])).
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
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X33)
% 0.22/0.52          | ~ (v2_pre_topc @ X33)
% 0.22/0.52          | ~ (l1_pre_topc @ X33)
% 0.22/0.52          | ~ (m1_pre_topc @ X34 @ X35)
% 0.22/0.52          | ((k2_tmap_1 @ X35 @ X33 @ X36 @ X34)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ 
% 0.22/0.52                 X36 @ (u1_struct_0 @ X34)))
% 0.22/0.52          | ~ (m1_subset_1 @ X36 @ 
% 0.22/0.52               (k1_zfmisc_1 @ 
% 0.22/0.52                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 0.22/0.52          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 0.22/0.52          | ~ (v1_funct_1 @ X36)
% 0.22/0.52          | ~ (l1_pre_topc @ X35)
% 0.22/0.52          | ~ (v2_pre_topc @ X35)
% 0.22/0.52          | (v2_struct_0 @ X35))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X1 @ 
% 0.22/0.52             (k1_zfmisc_1 @ 
% 0.22/0.52              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.22/0.52          | (v2_struct_0 @ sk_B)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.52          | ~ (v1_funct_1 @ X1)
% 0.22/0.52          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.22/0.52          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.22/0.52              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.22/0.52                 X1 @ (u1_struct_0 @ X2)))
% 0.22/0.52          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.22/0.52  thf('80', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('81', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('82', plain, (((u1_struct_0 @ sk_B) = (k1_relat_1 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.22/0.52  thf('83', plain, (((u1_struct_0 @ sk_B) = (k1_relat_1 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X1 @ 
% 0.22/0.52             (k1_zfmisc_1 @ 
% 0.22/0.52              (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))))
% 0.22/0.52          | (v2_struct_0 @ sk_B)
% 0.22/0.52          | ~ (v1_funct_1 @ X1)
% 0.22/0.52          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0))
% 0.22/0.52          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.22/0.52              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ X0) @ X1 @ 
% 0.22/0.52                 (u1_struct_0 @ X2)))
% 0.22/0.52          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.52          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.52              = (k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52                 sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.52          | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['74', '84'])).
% 0.22/0.52  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['21', '48'])).
% 0.22/0.52  thf(redefinition_k2_partfun1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.22/0.52  thf('89', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.22/0.52          | ~ (v1_funct_1 @ X16)
% 0.22/0.52          | ((k2_partfun1 @ X17 @ X18 @ X16 @ X19) = (k7_relat_1 @ X16 @ X19)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.22/0.52  thf('90', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['88', '89'])).
% 0.22/0.52  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('92', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k2_partfun1 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ X0)
% 0.22/0.52           = (k7_relat_1 @ sk_D @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.52  thf('93', plain,
% 0.22/0.52      ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.52  thf('94', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ sk_A)
% 0.22/0.52          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.52          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.52              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.52          | (v2_struct_0 @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['85', '86', '87', '92', '93', '94'])).
% 0.22/0.52  thf('96', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.52            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['73', '95'])).
% 0.22/0.52  thf('97', plain, (((k1_relat_1 @ sk_D) = (u1_struct_0 @ sk_C))),
% 0.22/0.52      inference('clc', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('98', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_B)
% 0.22/0.52        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.52            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))
% 0.22/0.52        | (v2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['96', '97'])).
% 0.22/0.52  thf('99', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('100', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.52            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 0.22/0.52      inference('clc', [status(thm)], ['98', '99'])).
% 0.22/0.52  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('102', plain,
% 0.22/0.52      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.52         = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.22/0.52      inference('clc', [status(thm)], ['100', '101'])).
% 0.22/0.52  thf('103', plain,
% 0.22/0.52      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.52          (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['72', '102'])).
% 0.22/0.52  thf('104', plain,
% 0.22/0.52      ((~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52           (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.52        | ~ (v1_relat_1 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['66', '103'])).
% 0.22/0.52  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('106', plain,
% 0.22/0.52      (~ (r1_funct_2 @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.52          (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['104', '105'])).
% 0.22/0.52  thf('107', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['62', '106'])).
% 0.22/0.52  thf('108', plain,
% 0.22/0.52      (![X22 : $i]:
% 0.22/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.22/0.52          | ~ (l1_struct_0 @ X22)
% 0.22/0.52          | (v2_struct_0 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.52  thf('109', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['107', '108'])).
% 0.22/0.52  thf('110', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.52  thf('111', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['109', '110'])).
% 0.22/0.52  thf('112', plain, ($false), inference('demod', [status(thm)], ['0', '111'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
