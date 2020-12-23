%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BAweVl7Jrq

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:45 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  140 (1019 expanded)
%              Number of leaves         :   38 ( 307 expanded)
%              Depth                    :   24
%              Number of atoms          : 1396 (21556 expanded)
%              Number of equality atoms :   30 ( 361 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_pre_topc @ X36 @ X37 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('12',plain,(
    ! [X38: $i] :
      ( ( m1_pre_topc @ X38 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( m1_pre_topc @ X25 @ ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ ( g1_pre_topc @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) ) )
      | ( m1_pre_topc @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_pre_topc @ X36 @ X37 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('30',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','33'])).

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

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( r1_funct_2 @ X27 @ X28 @ X31 @ X29 @ X26 @ X30 )
      | ( X26 != X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('37',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r1_funct_2 @ X27 @ X28 @ X31 @ X29 @ X30 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X29 )
      | ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['38','39','42'])).

thf('44',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('46',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('50',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','33'])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','32'])).

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

thf('54',plain,(
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

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','33'])).

thf(t40_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf('75',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X17 ) ) )
      | ( r2_relset_1 @ X14 @ X17 @ ( k2_partfun1 @ X14 @ X17 @ X16 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_2])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','33'])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('82',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('86',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( X6 = X9 )
      | ~ ( r2_relset_1 @ X7 @ X8 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ X1 )
      | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','33'])).

thf('90',plain,
    ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference('sup+',[status(thm)],['71','90'])).

thf('92',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['50','91'])).

thf('93',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','92'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('94',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('97',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BAweVl7Jrq
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:48 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 175 iterations in 0.091s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.36/0.55  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.55  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(t60_tmap_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.55                     ( v1_funct_2 @
% 0.36/0.55                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                     ( m1_subset_1 @
% 0.36/0.55                       D @ 
% 0.36/0.55                       ( k1_zfmisc_1 @
% 0.36/0.55                         ( k2_zfmisc_1 @
% 0.36/0.55                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55                   ( ( ( g1_pre_topc @
% 0.36/0.55                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.36/0.55                       ( g1_pre_topc @
% 0.36/0.55                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.36/0.55                     ( r1_funct_2 @
% 0.36/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.55                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.36/0.55                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.55            ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55                ( l1_pre_topc @ B ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.36/0.55                  ( ![D:$i]:
% 0.36/0.55                    ( ( ( v1_funct_1 @ D ) & 
% 0.36/0.55                        ( v1_funct_2 @
% 0.36/0.55                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.36/0.55                        ( m1_subset_1 @
% 0.36/0.55                          D @ 
% 0.36/0.55                          ( k1_zfmisc_1 @
% 0.36/0.55                            ( k2_zfmisc_1 @
% 0.36/0.55                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.36/0.55                      ( ( ( g1_pre_topc @
% 0.36/0.55                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.36/0.55                          ( g1_pre_topc @
% 0.36/0.55                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.36/0.55                        ( r1_funct_2 @
% 0.36/0.55                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.55                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.36/0.55                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.36/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t1_tsep_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.55           ( m1_subset_1 @
% 0.36/0.55             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X36 : $i, X37 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X36 @ X37)
% 0.36/0.55          | (m1_subset_1 @ (u1_struct_0 @ X36) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.36/0.55          | ~ (l1_pre_topc @ X37))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.36/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.36/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf(t3_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]:
% 0.36/0.55         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('8', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.55  thf(d10_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i]:
% 0.36/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.36/0.55        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.36/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t2_tsep_1, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X38 : $i]: ((m1_pre_topc @ X38 @ X38) | ~ (l1_pre_topc @ X38))),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.36/0.55  thf(t65_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( l1_pre_topc @ B ) =>
% 0.36/0.55           ( ( m1_pre_topc @ A @ B ) <=>
% 0.36/0.55             ( m1_pre_topc @
% 0.36/0.55               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X24 : $i, X25 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X24)
% 0.36/0.55          | ~ (m1_pre_topc @ X25 @ X24)
% 0.36/0.55          | (m1_pre_topc @ X25 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)))
% 0.36/0.55          | ~ (l1_pre_topc @ X25))),
% 0.36/0.55      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (m1_pre_topc @ X0 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_pre_topc @ X0 @ 
% 0.36/0.55           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (((m1_pre_topc @ sk_B @ 
% 0.36/0.55         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_B))),
% 0.36/0.55      inference('sup+', [status(thm)], ['11', '15'])).
% 0.36/0.55  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      ((m1_pre_topc @ sk_B @ 
% 0.36/0.55        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf(t59_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @
% 0.36/0.55             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.36/0.55           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X22 : $i, X23 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X22 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23)))
% 0.36/0.55          | (m1_pre_topc @ X22 @ X23)
% 0.36/0.55          | ~ (l1_pre_topc @ X23))),
% 0.36/0.55      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.36/0.55  thf('20', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_m1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X19 : $i, X20 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X19 @ X20)
% 0.36/0.55          | (l1_pre_topc @ X19)
% 0.36/0.55          | ~ (l1_pre_topc @ X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.55  thf('23', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('25', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '25'])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X36 : $i, X37 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X36 @ X37)
% 0.36/0.55          | (m1_subset_1 @ (u1_struct_0 @ X36) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.36/0.55          | ~ (l1_pre_topc @ X37))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_C)
% 0.36/0.55        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]:
% 0.36/0.55         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('32', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.55  thf('33', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '33'])).
% 0.36/0.55  thf(redefinition_r1_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.36/0.55         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.36/0.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.36/0.55       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.36/0.55          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.36/0.55          | ~ (v1_funct_1 @ X26)
% 0.36/0.55          | (v1_xboole_0 @ X29)
% 0.36/0.55          | (v1_xboole_0 @ X28)
% 0.36/0.55          | ~ (v1_funct_1 @ X30)
% 0.36/0.55          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.36/0.55          | (r1_funct_2 @ X27 @ X28 @ X31 @ X29 @ X26 @ X30)
% 0.36/0.55          | ((X26) != (X30)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.55         ((r1_funct_2 @ X27 @ X28 @ X31 @ X29 @ X30 @ X30)
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.36/0.55          | ~ (v1_funct_2 @ X30 @ X31 @ X29)
% 0.36/0.55          | (v1_xboole_0 @ X28)
% 0.36/0.55          | (v1_xboole_0 @ X29)
% 0.36/0.55          | ~ (v1_funct_1 @ X30)
% 0.36/0.55          | ~ (v1_funct_2 @ X30 @ X27 @ X28)
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.36/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (v1_xboole_0 @ X0)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.55             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '37'])).
% 0.36/0.55  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('41', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '32'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.36/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (v1_xboole_0 @ X0)
% 0.36/0.55          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.36/0.55             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['38', '39', '42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['34', '43'])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.36/0.55      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('49', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '32'])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.55  thf('51', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '33'])).
% 0.36/0.55  thf('53', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '32'])).
% 0.36/0.55  thf(d4_tmap_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.36/0.55             ( l1_pre_topc @ B ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.55                 ( m1_subset_1 @
% 0.36/0.55                   C @ 
% 0.36/0.55                   ( k1_zfmisc_1 @
% 0.36/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.55               ( ![D:$i]:
% 0.36/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.36/0.55                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.36/0.55                     ( k2_partfun1 @
% 0.36/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.55                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X32)
% 0.36/0.55          | ~ (v2_pre_topc @ X32)
% 0.36/0.55          | ~ (l1_pre_topc @ X32)
% 0.36/0.55          | ~ (m1_pre_topc @ X33 @ X34)
% 0.36/0.55          | ((k2_tmap_1 @ X34 @ X32 @ X35 @ X33)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32) @ 
% 0.36/0.55                 X35 @ (u1_struct_0 @ X33)))
% 0.36/0.55          | ~ (m1_subset_1 @ X35 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))))
% 0.36/0.55          | ~ (v1_funct_2 @ X35 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))
% 0.36/0.55          | ~ (v1_funct_1 @ X35)
% 0.36/0.55          | ~ (l1_pre_topc @ X34)
% 0.36/0.55          | ~ (v2_pre_topc @ X34)
% 0.36/0.55          | (v2_struct_0 @ X34))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.36/0.55             (k1_zfmisc_1 @ 
% 0.36/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.36/0.55          | (v2_struct_0 @ sk_B)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.55          | ~ (v1_funct_1 @ X1)
% 0.36/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.36/0.55          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.36/0.55                 X1 @ (u1_struct_0 @ X2)))
% 0.36/0.55          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.55  thf('56', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('58', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '32'])).
% 0.36/0.55  thf('59', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '32'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.36/0.55             (k1_zfmisc_1 @ 
% 0.36/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.36/0.55          | (v2_struct_0 @ sk_B)
% 0.36/0.55          | ~ (v1_funct_1 @ X1)
% 0.36/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.36/0.55          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.36/0.55                 X1 @ (u1_struct_0 @ X2)))
% 0.36/0.55          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | (v2_struct_0 @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.36/0.55  thf('61', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55                 sk_D @ (u1_struct_0 @ X0)))
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['52', '60'])).
% 0.36/0.55  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('64', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('66', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_A)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55                 sk_D @ (u1_struct_0 @ X0)))
% 0.36/0.55          | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 0.36/0.55  thf('67', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B)
% 0.36/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               sk_D @ (u1_struct_0 @ sk_C)))
% 0.36/0.55        | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['51', '66'])).
% 0.36/0.55  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               sk_D @ (u1_struct_0 @ sk_C))))),
% 0.36/0.55      inference('clc', [status(thm)], ['67', '68'])).
% 0.36/0.55  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('71', plain,
% 0.36/0.55      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['69', '70'])).
% 0.36/0.55  thf('72', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('73', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.55      inference('simplify', [status(thm)], ['72'])).
% 0.36/0.55  thf('74', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '33'])).
% 0.36/0.55  thf(t40_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( r1_tarski @ A @ C ) =>
% 0.36/0.55         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.36/0.55  thf('75', plain,
% 0.36/0.55      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X14 @ X15)
% 0.36/0.55          | ~ (v1_funct_1 @ X16)
% 0.36/0.55          | ~ (v1_funct_2 @ X16 @ X14 @ X17)
% 0.36/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X17)))
% 0.36/0.55          | (r2_relset_1 @ X14 @ X17 @ (k2_partfun1 @ X14 @ X17 @ X16 @ X15) @ 
% 0.36/0.55             X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [t40_funct_2])).
% 0.36/0.55  thf('76', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            X0) @ 
% 0.36/0.55           sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['74', '75'])).
% 0.36/0.55  thf('77', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.55  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('79', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            X0) @ 
% 0.36/0.55           sk_D)
% 0.36/0.55          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.36/0.55  thf('80', plain,
% 0.36/0.55      ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55        (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55         (u1_struct_0 @ sk_C)) @ 
% 0.36/0.55        sk_D)),
% 0.36/0.55      inference('sup-', [status(thm)], ['73', '79'])).
% 0.36/0.55  thf('81', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '33'])).
% 0.36/0.55  thf(dt_k2_partfun1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.36/0.55         ( m1_subset_1 @
% 0.36/0.55           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.36/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.36/0.55  thf('82', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.36/0.55          | ~ (v1_funct_1 @ X10)
% 0.36/0.55          | (m1_subset_1 @ (k2_partfun1 @ X11 @ X12 @ X10 @ X13) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.36/0.55  thf('83', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ 
% 0.36/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            X0) @ 
% 0.36/0.55           (k1_zfmisc_1 @ 
% 0.36/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['81', '82'])).
% 0.36/0.55  thf('84', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('85', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (m1_subset_1 @ 
% 0.36/0.55          (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55           X0) @ 
% 0.36/0.55          (k1_zfmisc_1 @ 
% 0.36/0.55           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['83', '84'])).
% 0.36/0.55  thf(redefinition_r2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.36/0.55  thf('86', plain,
% 0.36/0.55      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.36/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.36/0.55          | ((X6) = (X9))
% 0.36/0.55          | ~ (r2_relset_1 @ X7 @ X8 @ X6 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.36/0.55  thf('87', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55             (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55              sk_D @ X0) @ 
% 0.36/0.55             X1)
% 0.36/0.55          | ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55              sk_D @ X0) = (X1))
% 0.36/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['85', '86'])).
% 0.36/0.55  thf('88', plain,
% 0.36/0.55      ((~ (m1_subset_1 @ sk_D @ 
% 0.36/0.55           (k1_zfmisc_1 @ 
% 0.36/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.36/0.55        | ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            (u1_struct_0 @ sk_C)) = (sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['80', '87'])).
% 0.36/0.55  thf('89', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '33'])).
% 0.36/0.55  thf('90', plain,
% 0.36/0.55      (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55         (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['88', '89'])).
% 0.36/0.55  thf('91', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.36/0.55      inference('sup+', [status(thm)], ['71', '90'])).
% 0.36/0.55  thf('92', plain,
% 0.36/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['50', '91'])).
% 0.36/0.55  thf('93', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['47', '92'])).
% 0.36/0.55  thf(fc2_struct_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('94', plain,
% 0.36/0.55      (![X21 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.36/0.55          | ~ (l1_struct_0 @ X21)
% 0.36/0.55          | (v2_struct_0 @ X21))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.55  thf('95', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['93', '94'])).
% 0.36/0.55  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_l1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.55  thf('97', plain,
% 0.36/0.55      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.36/0.55  thf('99', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['95', '98'])).
% 0.36/0.55  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
