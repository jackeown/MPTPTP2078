%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pCeW4i21D6

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:45 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  180 (2505 expanded)
%              Number of leaves         :   41 ( 745 expanded)
%              Depth                    :   28
%              Number of atoms          : 1718 (64418 expanded)
%              Number of equality atoms :   39 (1075 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

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
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
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

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( m1_pre_topc @ X26 @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','18','19','20'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) )
      | ( m1_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('25',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X37 ) @ ( u1_pre_topc @ X37 ) ) @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('29',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ( X39
       != ( g1_pre_topc @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) ) )
      | ~ ( m1_pre_topc @ X39 @ X41 )
      | ( m1_pre_topc @ X40 @ X41 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('32',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ( m1_pre_topc @ X40 @ X41 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) ) @ X41 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X37 ) @ ( u1_pre_topc @ X37 ) ) @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('45',plain,(
    ! [X22: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('46',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['33','42','43','49','50','51','52'])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['29','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('56',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['16','17'])).

thf('60',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','63'])).

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

thf('66',plain,(
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

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('73',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('76',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('80',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','63'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

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

thf('84',plain,(
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

thf('85',plain,(
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
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('90',plain,(
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
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
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
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf('105',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X17 ) ) )
      | ( r2_relset_1 @ X14 @ X17 @ ( k2_partfun1 @ X14 @ X17 @ X16 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_2])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('111',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('116',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('121',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','62'])).

thf('122',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('123',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ( X6 = X9 )
      | ~ ( r2_relset_1 @ X7 @ X8 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ X1 )
      | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['114','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','63'])).

thf('127',plain,
    ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference('sup+',[status(thm)],['101','127'])).

thf('129',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['80','128'])).

thf('130',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','129'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('131',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('134',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('135',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['132','135'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['0','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pCeW4i21D6
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 382 iterations in 0.216s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.67  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.67  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.46/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.67  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.67  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.46/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.67  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.67  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.46/0.67  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.46/0.67  thf(t60_tmap_1, conjecture,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.46/0.67             ( l1_pre_topc @ B ) ) =>
% 0.46/0.67           ( ![C:$i]:
% 0.46/0.67             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.46/0.67               ( ![D:$i]:
% 0.46/0.67                 ( ( ( v1_funct_1 @ D ) & 
% 0.46/0.67                     ( v1_funct_2 @
% 0.46/0.67                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.67                     ( m1_subset_1 @
% 0.46/0.67                       D @ 
% 0.46/0.67                       ( k1_zfmisc_1 @
% 0.46/0.67                         ( k2_zfmisc_1 @
% 0.46/0.67                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.46/0.67                   ( ( ( g1_pre_topc @
% 0.46/0.67                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.46/0.67                       ( g1_pre_topc @
% 0.46/0.67                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.67                     ( r1_funct_2 @
% 0.46/0.67                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.67                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.46/0.67                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i]:
% 0.46/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.67            ( l1_pre_topc @ A ) ) =>
% 0.46/0.67          ( ![B:$i]:
% 0.46/0.67            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.46/0.67                ( l1_pre_topc @ B ) ) =>
% 0.46/0.67              ( ![C:$i]:
% 0.46/0.67                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.46/0.67                  ( ![D:$i]:
% 0.46/0.67                    ( ( ( v1_funct_1 @ D ) & 
% 0.46/0.67                        ( v1_funct_2 @
% 0.46/0.67                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.67                        ( m1_subset_1 @
% 0.46/0.67                          D @ 
% 0.46/0.67                          ( k1_zfmisc_1 @
% 0.46/0.67                            ( k2_zfmisc_1 @
% 0.46/0.67                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.46/0.67                      ( ( ( g1_pre_topc @
% 0.46/0.67                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.46/0.67                          ( g1_pre_topc @
% 0.46/0.67                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.67                        ( r1_funct_2 @
% 0.46/0.67                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.67                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.46/0.67                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.46/0.67  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_D @ 
% 0.46/0.67        (k1_zfmisc_1 @ 
% 0.46/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t1_tsep_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.67           ( m1_subset_1 @
% 0.46/0.67             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X42 : $i, X43 : $i]:
% 0.46/0.67         (~ (m1_pre_topc @ X42 @ X43)
% 0.46/0.67          | (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.46/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.46/0.67          | ~ (l1_pre_topc @ X43))),
% 0.46/0.67      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.67        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.46/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.46/0.67      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.67  thf(t3_subset, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X3 : $i, X4 : $i]:
% 0.46/0.67         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.67  thf('8', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.67  thf(d10_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X0 : $i, X2 : $i]:
% 0.46/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.46/0.67        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.67  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t65_pre_topc, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( l1_pre_topc @ B ) =>
% 0.46/0.67           ( ( m1_pre_topc @ A @ B ) <=>
% 0.46/0.67             ( m1_pre_topc @
% 0.46/0.67               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.46/0.67  thf('12', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i]:
% 0.46/0.67         (~ (l1_pre_topc @ X25)
% 0.46/0.67          | ~ (m1_pre_topc @ X26 @ X25)
% 0.46/0.67          | (m1_pre_topc @ X26 @ 
% 0.46/0.67             (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))
% 0.46/0.67          | ~ (l1_pre_topc @ X26))),
% 0.46/0.67      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      ((~ (l1_pre_topc @ sk_C)
% 0.46/0.67        | (m1_pre_topc @ sk_C @ 
% 0.46/0.67           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.67        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.67  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(dt_m1_pre_topc, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X19 : $i, X20 : $i]:
% 0.46/0.67         (~ (m1_pre_topc @ X19 @ X20)
% 0.46/0.67          | (l1_pre_topc @ X19)
% 0.46/0.67          | ~ (l1_pre_topc @ X20))),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.67  thf('16', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.67  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('18', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.46/0.67         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      ((m1_pre_topc @ sk_C @ 
% 0.46/0.67        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.67      inference('demod', [status(thm)], ['13', '18', '19', '20'])).
% 0.46/0.67  thf(t59_pre_topc, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_pre_topc @
% 0.46/0.67             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.46/0.67           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X23 : $i, X24 : $i]:
% 0.46/0.67         (~ (m1_pre_topc @ X23 @ 
% 0.46/0.67             (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)))
% 0.46/0.67          | (m1_pre_topc @ X23 @ X24)
% 0.46/0.67          | ~ (l1_pre_topc @ X24))),
% 0.46/0.67      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.46/0.67  thf('23', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_C @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.67  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf('25', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.67  thf(t11_tmap_1, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_pre_topc @ A ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.67           ( ( v1_pre_topc @
% 0.46/0.67               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.46/0.67             ( m1_pre_topc @
% 0.46/0.67               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X37 : $i, X38 : $i]:
% 0.46/0.67         (~ (m1_pre_topc @ X37 @ X38)
% 0.46/0.67          | (m1_pre_topc @ 
% 0.46/0.67             (g1_pre_topc @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37)) @ X38)
% 0.46/0.67          | ~ (l1_pre_topc @ X38))),
% 0.46/0.67      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      ((~ (l1_pre_topc @ sk_C)
% 0.46/0.67        | (m1_pre_topc @ 
% 0.46/0.67           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C))),
% 0.46/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.67  thf('28', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf('29', plain,
% 0.46/0.67      ((m1_pre_topc @ 
% 0.46/0.67        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)),
% 0.46/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.46/0.68         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t12_tmap_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.46/0.68               ( ( ( B ) =
% 0.46/0.68                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.46/0.68                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.68         (~ (v2_pre_topc @ X39)
% 0.46/0.68          | ~ (l1_pre_topc @ X39)
% 0.46/0.68          | ((X39) != (g1_pre_topc @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40)))
% 0.46/0.68          | ~ (m1_pre_topc @ X39 @ X41)
% 0.46/0.68          | (m1_pre_topc @ X40 @ X41)
% 0.46/0.68          | ~ (l1_pre_topc @ X40)
% 0.46/0.68          | ~ (v2_pre_topc @ X40)
% 0.46/0.68          | ~ (l1_pre_topc @ X41))),
% 0.46/0.68      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X40 : $i, X41 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ X41)
% 0.46/0.68          | ~ (v2_pre_topc @ X40)
% 0.46/0.68          | ~ (l1_pre_topc @ X40)
% 0.46/0.68          | (m1_pre_topc @ X40 @ X41)
% 0.46/0.68          | ~ (m1_pre_topc @ 
% 0.46/0.68               (g1_pre_topc @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40)) @ X41)
% 0.46/0.68          | ~ (l1_pre_topc @ 
% 0.46/0.68               (g1_pre_topc @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40)))
% 0.46/0.68          | ~ (v2_pre_topc @ 
% 0.46/0.68               (g1_pre_topc @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40))))),
% 0.46/0.68      inference('simplify', [status(thm)], ['31'])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (l1_pre_topc @ 
% 0.46/0.68             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.68          | ~ (v2_pre_topc @ 
% 0.46/0.68               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.46/0.68          | ~ (m1_pre_topc @ 
% 0.46/0.68               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.46/0.68          | (m1_pre_topc @ sk_B @ X0)
% 0.46/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.46/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.46/0.68          | ~ (l1_pre_topc @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['30', '32'])).
% 0.46/0.68  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X37 : $i, X38 : $i]:
% 0.46/0.68         (~ (m1_pre_topc @ X37 @ X38)
% 0.46/0.68          | (m1_pre_topc @ 
% 0.46/0.68             (g1_pre_topc @ (u1_struct_0 @ X37) @ (u1_pre_topc @ X37)) @ X38)
% 0.46/0.68          | ~ (l1_pre_topc @ X38))),
% 0.46/0.68      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.68        | (m1_pre_topc @ 
% 0.46/0.68           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.68  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      ((m1_pre_topc @ 
% 0.46/0.68        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B)),
% 0.46/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i]:
% 0.46/0.68         (~ (m1_pre_topc @ X19 @ X20)
% 0.46/0.68          | (l1_pre_topc @ X19)
% 0.46/0.68          | ~ (l1_pre_topc @ X20))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.68        | (l1_pre_topc @ 
% 0.46/0.68           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.68  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      ((l1_pre_topc @ 
% 0.46/0.68        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.46/0.68         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.46/0.68         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(fc6_pre_topc, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68       ( ( v1_pre_topc @
% 0.46/0.68           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.46/0.68         ( v2_pre_topc @
% 0.46/0.68           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      (![X22 : $i]:
% 0.46/0.68         ((v2_pre_topc @ 
% 0.46/0.68           (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.46/0.68          | ~ (l1_pre_topc @ X22)
% 0.46/0.68          | ~ (v2_pre_topc @ X22))),
% 0.46/0.68      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.46/0.68  thf('46', plain,
% 0.46/0.68      (((v2_pre_topc @ 
% 0.46/0.68         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.68        | ~ (v2_pre_topc @ sk_B)
% 0.46/0.68        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.68      inference('sup+', [status(thm)], ['44', '45'])).
% 0.46/0.68  thf('47', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('49', plain,
% 0.46/0.68      ((v2_pre_topc @ 
% 0.46/0.68        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.46/0.68         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('52', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('53', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (m1_pre_topc @ 
% 0.46/0.68             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.46/0.68          | (m1_pre_topc @ sk_B @ X0)
% 0.46/0.68          | ~ (l1_pre_topc @ X0))),
% 0.46/0.68      inference('demod', [status(thm)],
% 0.46/0.68                ['33', '42', '43', '49', '50', '51', '52'])).
% 0.46/0.68  thf('54', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['29', '53'])).
% 0.46/0.68  thf('55', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('56', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.46/0.68      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      (![X42 : $i, X43 : $i]:
% 0.46/0.68         (~ (m1_pre_topc @ X42 @ X43)
% 0.46/0.68          | (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.46/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.46/0.68          | ~ (l1_pre_topc @ X43))),
% 0.46/0.68      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.68  thf('58', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_C)
% 0.46/0.68        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.46/0.68  thf('59', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.46/0.68      inference('demod', [status(thm)], ['58', '59'])).
% 0.46/0.68  thf('61', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i]:
% 0.46/0.68         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.68  thf('62', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.68  thf('63', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ 
% 0.46/0.68        (k1_zfmisc_1 @ 
% 0.46/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['1', '63'])).
% 0.46/0.68  thf('65', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ 
% 0.46/0.68        (k1_zfmisc_1 @ 
% 0.46/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['1', '63'])).
% 0.46/0.68  thf(reflexivity_r1_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.68     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.68         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.46/0.68         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.68         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.46/0.68         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.68       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 0.46/0.68  thf('66', plain,
% 0.46/0.68      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.46/0.68         ((r1_funct_2 @ X27 @ X28 @ X29 @ X30 @ X31 @ X31)
% 0.46/0.68          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.46/0.68          | ~ (v1_funct_2 @ X31 @ X27 @ X28)
% 0.46/0.68          | ~ (v1_funct_1 @ X31)
% 0.46/0.68          | (v1_xboole_0 @ X30)
% 0.46/0.68          | (v1_xboole_0 @ X28)
% 0.46/0.68          | ~ (v1_funct_1 @ X32)
% 0.46/0.68          | ~ (v1_funct_2 @ X32 @ X29 @ X30)
% 0.46/0.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.68      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.46/0.68          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.46/0.68          | ~ (v1_funct_1 @ X2)
% 0.46/0.68          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.68          | (v1_xboole_0 @ X0)
% 0.46/0.68          | ~ (v1_funct_1 @ sk_D)
% 0.46/0.68          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.46/0.68          | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.46/0.68             X0 @ sk_D @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.68  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('70', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('71', plain,
% 0.46/0.68      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.68  thf('72', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.46/0.68          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.46/0.68          | ~ (v1_funct_1 @ X2)
% 0.46/0.68          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.68          | (v1_xboole_0 @ X0)
% 0.46/0.68          | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.46/0.68             X0 @ sk_D @ sk_D))),
% 0.46/0.68      inference('demod', [status(thm)], ['67', '68', '71'])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.46/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.68        | ~ (v1_funct_1 @ sk_D)
% 0.46/0.68        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['64', '72'])).
% 0.46/0.68  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('75', plain,
% 0.46/0.68      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.68  thf('76', plain,
% 0.46/0.68      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.46/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.68      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.46/0.68  thf('77', plain,
% 0.46/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.68        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.46/0.68      inference('simplify', [status(thm)], ['76'])).
% 0.46/0.68  thf('78', plain,
% 0.46/0.68      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('79', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('80', plain,
% 0.46/0.68      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['78', '79'])).
% 0.46/0.68  thf('81', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('82', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ 
% 0.46/0.68        (k1_zfmisc_1 @ 
% 0.46/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['1', '63'])).
% 0.46/0.68  thf('83', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf(d4_tmap_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.46/0.68             ( l1_pre_topc @ B ) ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.68                 ( m1_subset_1 @
% 0.46/0.68                   C @ 
% 0.46/0.68                   ( k1_zfmisc_1 @
% 0.46/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.68               ( ![D:$i]:
% 0.46/0.68                 ( ( m1_pre_topc @ D @ A ) =>
% 0.46/0.68                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.46/0.68                     ( k2_partfun1 @
% 0.46/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.68                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf('84', plain,
% 0.46/0.68      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.68         ((v2_struct_0 @ X33)
% 0.46/0.68          | ~ (v2_pre_topc @ X33)
% 0.46/0.68          | ~ (l1_pre_topc @ X33)
% 0.46/0.68          | ~ (m1_pre_topc @ X34 @ X35)
% 0.46/0.68          | ((k2_tmap_1 @ X35 @ X33 @ X36 @ X34)
% 0.46/0.68              = (k2_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ 
% 0.46/0.68                 X36 @ (u1_struct_0 @ X34)))
% 0.46/0.68          | ~ (m1_subset_1 @ X36 @ 
% 0.46/0.68               (k1_zfmisc_1 @ 
% 0.46/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 0.46/0.68          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 0.46/0.68          | ~ (v1_funct_1 @ X36)
% 0.46/0.68          | ~ (l1_pre_topc @ X35)
% 0.46/0.68          | ~ (v2_pre_topc @ X35)
% 0.46/0.68          | (v2_struct_0 @ X35))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.46/0.68  thf('85', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.68             (k1_zfmisc_1 @ 
% 0.46/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.46/0.68          | (v2_struct_0 @ sk_B)
% 0.46/0.68          | ~ (v2_pre_topc @ sk_B)
% 0.46/0.68          | ~ (l1_pre_topc @ sk_B)
% 0.46/0.68          | ~ (v1_funct_1 @ X1)
% 0.46/0.68          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.46/0.68          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.46/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.46/0.68                 X1 @ (u1_struct_0 @ X2)))
% 0.46/0.68          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.46/0.68          | ~ (l1_pre_topc @ X0)
% 0.46/0.68          | ~ (v2_pre_topc @ X0)
% 0.46/0.68          | (v2_struct_0 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['83', '84'])).
% 0.46/0.68  thf('86', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('88', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('89', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('90', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.46/0.68             (k1_zfmisc_1 @ 
% 0.46/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.46/0.68          | (v2_struct_0 @ sk_B)
% 0.46/0.68          | ~ (v1_funct_1 @ X1)
% 0.46/0.68          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.46/0.68          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.46/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.46/0.68                 X1 @ (u1_struct_0 @ X2)))
% 0.46/0.68          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.46/0.68          | ~ (l1_pre_topc @ X0)
% 0.46/0.68          | ~ (v2_pre_topc @ X0)
% 0.46/0.68          | (v2_struct_0 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.46/0.68  thf('91', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((v2_struct_0 @ sk_A)
% 0.46/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.68          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.68          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.46/0.68          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.46/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68                 sk_D @ (u1_struct_0 @ X0)))
% 0.46/0.68          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.46/0.68          | ~ (v1_funct_1 @ sk_D)
% 0.46/0.68          | (v2_struct_0 @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['82', '90'])).
% 0.46/0.68  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('94', plain,
% 0.46/0.68      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.68  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('96', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((v2_struct_0 @ sk_A)
% 0.46/0.68          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.46/0.68          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.46/0.68              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68                 sk_D @ (u1_struct_0 @ X0)))
% 0.46/0.68          | (v2_struct_0 @ sk_B))),
% 0.46/0.68      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.46/0.68  thf('97', plain,
% 0.46/0.68      (((v2_struct_0 @ sk_B)
% 0.46/0.68        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.46/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68               sk_D @ (u1_struct_0 @ sk_C)))
% 0.46/0.68        | (v2_struct_0 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['81', '96'])).
% 0.46/0.68  thf('98', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('99', plain,
% 0.46/0.68      (((v2_struct_0 @ sk_A)
% 0.46/0.68        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.46/0.68            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68               sk_D @ (u1_struct_0 @ sk_C))))),
% 0.46/0.68      inference('clc', [status(thm)], ['97', '98'])).
% 0.46/0.68  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('101', plain,
% 0.46/0.68      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.46/0.68         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68            (u1_struct_0 @ sk_C)))),
% 0.46/0.68      inference('clc', [status(thm)], ['99', '100'])).
% 0.46/0.68  thf('102', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('103', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.68      inference('simplify', [status(thm)], ['102'])).
% 0.46/0.68  thf('104', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ 
% 0.46/0.68        (k1_zfmisc_1 @ 
% 0.46/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t40_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68       ( ( r1_tarski @ A @ C ) =>
% 0.46/0.68         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.46/0.68  thf('105', plain,
% 0.46/0.68      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X14 @ X15)
% 0.46/0.68          | ~ (v1_funct_1 @ X16)
% 0.46/0.68          | ~ (v1_funct_2 @ X16 @ X14 @ X17)
% 0.46/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X17)))
% 0.46/0.68          | (r2_relset_1 @ X14 @ X17 @ (k2_partfun1 @ X14 @ X17 @ X16 @ X15) @ 
% 0.46/0.68             X16))),
% 0.46/0.68      inference('cnf', [status(esa)], [t40_funct_2])).
% 0.46/0.68  thf('106', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68            X0) @ 
% 0.46/0.68           sk_D)
% 0.46/0.68          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.46/0.68          | ~ (v1_funct_1 @ sk_D)
% 0.46/0.68          | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['104', '105'])).
% 0.46/0.68  thf('107', plain,
% 0.46/0.68      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('109', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((r2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68            X0) @ 
% 0.46/0.68           sk_D)
% 0.46/0.68          | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.46/0.68  thf('110', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('111', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('112', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('113', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68            X0) @ 
% 0.46/0.68           sk_D)
% 0.46/0.68          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.46/0.68  thf('114', plain,
% 0.46/0.68      ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68        (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68         (u1_struct_0 @ sk_C)) @ 
% 0.46/0.68        sk_D)),
% 0.46/0.68      inference('sup-', [status(thm)], ['103', '113'])).
% 0.46/0.68  thf('115', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ 
% 0.46/0.68        (k1_zfmisc_1 @ 
% 0.46/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(dt_k2_partfun1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.46/0.68         ( m1_subset_1 @
% 0.46/0.68           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.46/0.68           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.46/0.68  thf('116', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.46/0.68          | ~ (v1_funct_1 @ X10)
% 0.46/0.68          | (m1_subset_1 @ (k2_partfun1 @ X11 @ X12 @ X10 @ X13) @ 
% 0.46/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.46/0.68  thf('117', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((m1_subset_1 @ 
% 0.46/0.68           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68            X0) @ 
% 0.46/0.68           (k1_zfmisc_1 @ 
% 0.46/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.46/0.68          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['115', '116'])).
% 0.46/0.68  thf('118', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('119', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (m1_subset_1 @ 
% 0.46/0.68          (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68           X0) @ 
% 0.46/0.68          (k1_zfmisc_1 @ 
% 0.46/0.68           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['117', '118'])).
% 0.46/0.68  thf('120', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('121', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '62'])).
% 0.46/0.68  thf('122', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (m1_subset_1 @ 
% 0.46/0.68          (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68           X0) @ 
% 0.46/0.68          (k1_zfmisc_1 @ 
% 0.46/0.68           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.46/0.68  thf(redefinition_r2_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.68  thf('123', plain,
% 0.46/0.68      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.46/0.68          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.46/0.68          | ((X6) = (X9))
% 0.46/0.68          | ~ (r2_relset_1 @ X7 @ X8 @ X6 @ X9))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.68  thf('124', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68             (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68              sk_D @ X0) @ 
% 0.46/0.68             X1)
% 0.46/0.68          | ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68              sk_D @ X0) = (X1))
% 0.46/0.68          | ~ (m1_subset_1 @ X1 @ 
% 0.46/0.68               (k1_zfmisc_1 @ 
% 0.46/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['122', '123'])).
% 0.46/0.68  thf('125', plain,
% 0.46/0.68      ((~ (m1_subset_1 @ sk_D @ 
% 0.46/0.68           (k1_zfmisc_1 @ 
% 0.46/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.46/0.68        | ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68            (u1_struct_0 @ sk_C)) = (sk_D)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['114', '124'])).
% 0.46/0.68  thf('126', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D @ 
% 0.46/0.68        (k1_zfmisc_1 @ 
% 0.46/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['1', '63'])).
% 0.46/0.68  thf('127', plain,
% 0.46/0.68      (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.68         (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.46/0.68      inference('demod', [status(thm)], ['125', '126'])).
% 0.46/0.68  thf('128', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.46/0.68      inference('sup+', [status(thm)], ['101', '127'])).
% 0.46/0.68  thf('129', plain,
% 0.46/0.68      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.68          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.46/0.68      inference('demod', [status(thm)], ['80', '128'])).
% 0.46/0.68  thf('130', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['77', '129'])).
% 0.46/0.68  thf(fc2_struct_0, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.68       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.68  thf('131', plain,
% 0.46/0.68      (![X21 : $i]:
% 0.46/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.46/0.68          | ~ (l1_struct_0 @ X21)
% 0.46/0.68          | (v2_struct_0 @ X21))),
% 0.46/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.68  thf('132', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['130', '131'])).
% 0.46/0.68  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(dt_l1_pre_topc, axiom,
% 0.46/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.68  thf('134', plain,
% 0.46/0.68      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf('135', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.68      inference('sup-', [status(thm)], ['133', '134'])).
% 0.46/0.68  thf('136', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.68      inference('demod', [status(thm)], ['132', '135'])).
% 0.46/0.68  thf('137', plain, ($false), inference('demod', [status(thm)], ['0', '136'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
