%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kQEnyRxbVa

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:40 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  192 (2421 expanded)
%              Number of leaves         :   38 ( 701 expanded)
%              Depth                    :   29
%              Number of atoms          : 1838 (62403 expanded)
%              Number of equality atoms :   41 (1025 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('3',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('4',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( m1_pre_topc @ X24 @ ( g1_pre_topc @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ( m1_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['10','15'])).

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

thf('17',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X36 @ X37 )
      | ~ ( m1_pre_topc @ X36 @ X38 )
      | ( r1_tarski @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ( m1_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['22','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_pre_topc @ X36 @ X37 )
      | ~ ( m1_pre_topc @ X36 @ X38 )
      | ( r1_tarski @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_pre_topc @ X38 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','46'])).

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

thf('49',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r1_funct_2 @ X25 @ X26 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['50','51','54'])).

thf('56',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('59',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('63',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','46'])).

thf('66',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

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

thf('67',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( ( k2_tmap_1 @ X33 @ X31 @ X34 @ X32 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) @ X34 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('73',plain,(
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
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,(
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
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( m1_pre_topc @ X24 @ ( g1_pre_topc @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('89',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ( m1_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('95',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','46'])).

thf('97',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X33 )
      | ( ( k2_tmap_1 @ X33 @ X31 @ X34 @ X32 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) @ X34 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X33 ) @ ( u1_struct_0 @ X31 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v2_pre_topc @ sk_C )
      | ~ ( l1_pre_topc @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('100',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('101',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('106',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','104','105','106','107','108','109'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('117',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','46'])).

thf(t40_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf('119',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X14 ) ) )
      | ( r2_relset_1 @ X11 @ X14 @ ( k2_partfun1 @ X11 @ X14 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_2])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('122',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('126',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('128',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('129',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X8 @ X9 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('134',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['127','135'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('137',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( X3 = X6 )
      | ~ ( r2_relset_1 @ X4 @ X5 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['126','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','46'])).

thf('141',plain,
    ( ( k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( sk_D
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','141'])).

thf('143',plain,
    ( sk_D
    = ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['84','142'])).

thf('144',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['63','143'])).

thf('145',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','144'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('146',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('149',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('150',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['147','150'])).

thf('152',plain,(
    $false ),
    inference(demod,[status(thm)],['0','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kQEnyRxbVa
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 194 iterations in 0.080s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.36/0.55  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.36/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
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
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.36/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t2_tsep_1, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.36/0.55  thf(t65_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( l1_pre_topc @ B ) =>
% 0.36/0.55           ( ( m1_pre_topc @ A @ B ) <=>
% 0.36/0.55             ( m1_pre_topc @
% 0.36/0.55               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X23)
% 0.36/0.55          | ~ (m1_pre_topc @ X24 @ X23)
% 0.36/0.55          | (m1_pre_topc @ X24 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23)))
% 0.36/0.55          | ~ (l1_pre_topc @ X24))),
% 0.36/0.55      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (m1_pre_topc @ X0 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_pre_topc @ X0 @ 
% 0.36/0.55           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['6'])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (((m1_pre_topc @ sk_B @ 
% 0.36/0.55         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_B))),
% 0.36/0.55      inference('sup+', [status(thm)], ['3', '7'])).
% 0.36/0.55  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      ((m1_pre_topc @ sk_B @ 
% 0.36/0.55        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.36/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t59_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @
% 0.36/0.55             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.36/0.55           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X21 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.36/0.55          | (m1_pre_topc @ X21 @ X22)
% 0.36/0.55          | ~ (l1_pre_topc @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X0 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.36/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.55          | (m1_pre_topc @ X0 @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X0 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.36/0.55          | (m1_pre_topc @ X0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['10', '15'])).
% 0.36/0.55  thf(t4_tsep_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_pre_topc @ C @ A ) =>
% 0.36/0.55               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.36/0.55                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X36 @ X37)
% 0.36/0.55          | ~ (m1_pre_topc @ X36 @ X38)
% 0.36/0.55          | (r1_tarski @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))
% 0.36/0.55          | ~ (m1_pre_topc @ X38 @ X37)
% 0.36/0.55          | ~ (l1_pre_topc @ X37)
% 0.36/0.55          | ~ (v2_pre_topc @ X37))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ sk_B)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.36/0.55        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '21'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      ((m1_pre_topc @ sk_B @ 
% 0.36/0.55        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X21 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.36/0.55          | (m1_pre_topc @ X21 @ X22)
% 0.36/0.55          | ~ (l1_pre_topc @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.36/0.55  thf('25', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.55  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_m1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X18 : $i, X19 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X18 @ X19)
% 0.36/0.55          | (l1_pre_topc @ X18)
% 0.36/0.55          | ~ (l1_pre_topc @ X19))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.36/0.55  thf('28', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('30', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['25', '30'])).
% 0.36/0.55  thf('32', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['22', '31'])).
% 0.36/0.55  thf(d10_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i]:
% 0.36/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.36/0.55        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 0.36/0.55      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.36/0.55  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X36 @ X37)
% 0.36/0.55          | ~ (m1_pre_topc @ X36 @ X38)
% 0.36/0.55          | (r1_tarski @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X38))
% 0.36/0.55          | ~ (m1_pre_topc @ X38 @ X37)
% 0.36/0.55          | ~ (l1_pre_topc @ X37)
% 0.36/0.55          | ~ (v2_pre_topc @ X37))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ sk_B)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.55  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.36/0.55  thf('42', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.36/0.55        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.36/0.55        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['35', '41'])).
% 0.36/0.55  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('45', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.36/0.55  thf('46', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '45'])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '46'])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '46'])).
% 0.36/0.55  thf(reflexivity_r1_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.55     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.36/0.55         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.36/0.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.36/0.55       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.55         ((r1_funct_2 @ X25 @ X26 @ X27 @ X28 @ X29 @ X29)
% 0.36/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.36/0.55          | ~ (v1_funct_2 @ X29 @ X25 @ X26)
% 0.36/0.55          | ~ (v1_funct_1 @ X29)
% 0.36/0.55          | (v1_xboole_0 @ X28)
% 0.36/0.55          | (v1_xboole_0 @ X26)
% 0.36/0.55          | ~ (v1_funct_1 @ X30)
% 0.36/0.55          | ~ (v1_funct_2 @ X30 @ X27 @ X28)
% 0.36/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.36/0.55      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.36/0.55          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.36/0.55          | ~ (v1_funct_1 @ X2)
% 0.36/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (v1_xboole_0 @ X0)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.36/0.55             X0 @ sk_D @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.55  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('53', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '45'])).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.36/0.55          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.36/0.55          | ~ (v1_funct_1 @ X2)
% 0.36/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | (v1_xboole_0 @ X0)
% 0.36/0.55          | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.36/0.55             X0 @ sk_D @ sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['50', '51', '54'])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['47', '55'])).
% 0.36/0.55  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('58', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.55        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.36/0.55      inference('simplify', [status(thm)], ['59'])).
% 0.36/0.55  thf('61', plain,
% 0.36/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('62', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '45'])).
% 0.36/0.55  thf('63', plain,
% 0.36/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.36/0.55  thf('64', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('65', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '46'])).
% 0.36/0.55  thf('66', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '45'])).
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
% 0.36/0.55  thf('67', plain,
% 0.36/0.55      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X31)
% 0.36/0.55          | ~ (v2_pre_topc @ X31)
% 0.36/0.55          | ~ (l1_pre_topc @ X31)
% 0.36/0.55          | ~ (m1_pre_topc @ X32 @ X33)
% 0.36/0.55          | ((k2_tmap_1 @ X33 @ X31 @ X34 @ X32)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31) @ 
% 0.36/0.55                 X34 @ (u1_struct_0 @ X32)))
% 0.36/0.55          | ~ (m1_subset_1 @ X34 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))))
% 0.36/0.55          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))
% 0.36/0.55          | ~ (v1_funct_1 @ X34)
% 0.36/0.55          | ~ (l1_pre_topc @ X33)
% 0.36/0.55          | ~ (v2_pre_topc @ X33)
% 0.36/0.55          | (v2_struct_0 @ X33))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.36/0.55  thf('68', plain,
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
% 0.36/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.36/0.55  thf('69', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('71', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '45'])).
% 0.36/0.55  thf('72', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '45'])).
% 0.36/0.55  thf('73', plain,
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
% 0.36/0.55      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.36/0.55  thf('74', plain,
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
% 0.36/0.55      inference('sup-', [status(thm)], ['65', '73'])).
% 0.36/0.55  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('77', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.55  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('79', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_A)
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.36/0.55          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55                 sk_D @ (u1_struct_0 @ X0)))
% 0.36/0.55          | (v2_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 0.36/0.55  thf('80', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_B)
% 0.36/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               sk_D @ (u1_struct_0 @ sk_C)))
% 0.36/0.55        | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['64', '79'])).
% 0.36/0.55  thf('81', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('82', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               sk_D @ (u1_struct_0 @ sk_C))))),
% 0.36/0.55      inference('clc', [status(thm)], ['80', '81'])).
% 0.36/0.55  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('84', plain,
% 0.36/0.55      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.36/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['82', '83'])).
% 0.36/0.55  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('86', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X23)
% 0.36/0.55          | ~ (m1_pre_topc @ X24 @ X23)
% 0.36/0.55          | (m1_pre_topc @ X24 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23)))
% 0.36/0.55          | ~ (l1_pre_topc @ X24))),
% 0.36/0.55      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.36/0.55  thf('87', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_C)
% 0.36/0.55        | (m1_pre_topc @ sk_C @ 
% 0.36/0.55           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['85', '86'])).
% 0.36/0.55  thf('88', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('89', plain,
% 0.36/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.36/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('91', plain,
% 0.36/0.55      ((m1_pre_topc @ sk_C @ 
% 0.36/0.55        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.36/0.55  thf('92', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X21 @ 
% 0.36/0.55             (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.36/0.55          | (m1_pre_topc @ X21 @ X22)
% 0.36/0.55          | ~ (l1_pre_topc @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.36/0.55  thf('93', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_C @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.36/0.55  thf('94', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('95', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.36/0.55  thf('96', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '46'])).
% 0.36/0.55  thf('97', plain,
% 0.36/0.55      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.55         ((v2_struct_0 @ X31)
% 0.36/0.55          | ~ (v2_pre_topc @ X31)
% 0.36/0.55          | ~ (l1_pre_topc @ X31)
% 0.36/0.55          | ~ (m1_pre_topc @ X32 @ X33)
% 0.36/0.55          | ((k2_tmap_1 @ X33 @ X31 @ X34 @ X32)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31) @ 
% 0.36/0.55                 X34 @ (u1_struct_0 @ X32)))
% 0.36/0.55          | ~ (m1_subset_1 @ X34 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))))
% 0.36/0.55          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X33) @ (u1_struct_0 @ X31))
% 0.36/0.55          | ~ (v1_funct_1 @ X34)
% 0.36/0.55          | ~ (l1_pre_topc @ X33)
% 0.36/0.55          | ~ (v2_pre_topc @ X33)
% 0.36/0.55          | (v2_struct_0 @ X33))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.36/0.55  thf('98', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_C)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_C)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_C)
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ X0)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55                 sk_D @ (u1_struct_0 @ X0)))
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.36/0.55  thf('99', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.36/0.55  thf('100', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         (~ (m1_pre_topc @ X15 @ X16)
% 0.36/0.55          | (v2_pre_topc @ X15)
% 0.36/0.55          | ~ (l1_pre_topc @ X16)
% 0.36/0.55          | ~ (v2_pre_topc @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.36/0.55  thf('101', plain,
% 0.36/0.55      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['99', '100'])).
% 0.36/0.55  thf('102', plain, ((v2_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('104', plain, ((v2_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.36/0.55  thf('105', plain, ((l1_pre_topc @ sk_C)),
% 0.36/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.55  thf('106', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('107', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.55  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('110', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v2_struct_0 @ sk_C)
% 0.36/0.55          | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ X0)
% 0.36/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55                 sk_D @ (u1_struct_0 @ X0)))
% 0.36/0.55          | ~ (m1_pre_topc @ X0 @ sk_C)
% 0.36/0.55          | (v2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)],
% 0.36/0.55                ['98', '104', '105', '106', '107', '108', '109'])).
% 0.36/0.55  thf('111', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_A)
% 0.36/0.55        | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 0.36/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               sk_D @ (u1_struct_0 @ sk_C)))
% 0.36/0.55        | (v2_struct_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['95', '110'])).
% 0.36/0.55  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('113', plain,
% 0.36/0.55      (((v2_struct_0 @ sk_C)
% 0.36/0.55        | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 0.36/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55               sk_D @ (u1_struct_0 @ sk_C))))),
% 0.36/0.55      inference('clc', [status(thm)], ['111', '112'])).
% 0.36/0.55  thf('114', plain, (~ (v2_struct_0 @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('115', plain,
% 0.36/0.55      (((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 0.36/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['113', '114'])).
% 0.36/0.55  thf('116', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('117', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.55      inference('simplify', [status(thm)], ['116'])).
% 0.36/0.55  thf('118', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '46'])).
% 0.36/0.55  thf(t40_funct_2, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( r1_tarski @ A @ C ) =>
% 0.36/0.55         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.36/0.55  thf('119', plain,
% 0.36/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         (~ (r1_tarski @ X11 @ X12)
% 0.36/0.55          | ~ (v1_funct_1 @ X13)
% 0.36/0.55          | ~ (v1_funct_2 @ X13 @ X11 @ X14)
% 0.36/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X14)))
% 0.36/0.55          | (r2_relset_1 @ X11 @ X14 @ (k2_partfun1 @ X11 @ X14 @ X13 @ X12) @ 
% 0.36/0.55             X13))),
% 0.36/0.55      inference('cnf', [status(esa)], [t40_funct_2])).
% 0.36/0.55  thf('120', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            X0) @ 
% 0.36/0.55           sk_D)
% 0.36/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.36/0.55          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['118', '119'])).
% 0.36/0.55  thf('121', plain,
% 0.36/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.36/0.55  thf('122', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('123', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            X0) @ 
% 0.36/0.55           sk_D)
% 0.36/0.55          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['120', '121', '122'])).
% 0.36/0.55  thf('124', plain,
% 0.36/0.55      ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55        (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55         (u1_struct_0 @ sk_C)) @ 
% 0.36/0.55        sk_D)),
% 0.36/0.55      inference('sup-', [status(thm)], ['117', '123'])).
% 0.36/0.55  thf('125', plain,
% 0.36/0.55      (((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 0.36/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['113', '114'])).
% 0.36/0.55  thf('126', plain,
% 0.36/0.55      ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55        (k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['124', '125'])).
% 0.36/0.55  thf('127', plain,
% 0.36/0.55      (((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C)
% 0.36/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('clc', [status(thm)], ['113', '114'])).
% 0.36/0.55  thf('128', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k2_partfun1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.36/0.55         ( m1_subset_1 @
% 0.36/0.55           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.36/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.36/0.55  thf('129', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.36/0.55          | ~ (v1_funct_1 @ X7)
% 0.36/0.55          | (m1_subset_1 @ (k2_partfun1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.36/0.55  thf('130', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ 
% 0.36/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            X0) @ 
% 0.36/0.55           (k1_zfmisc_1 @ 
% 0.36/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.36/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.36/0.55      inference('sup-', [status(thm)], ['128', '129'])).
% 0.36/0.55  thf('131', plain, ((v1_funct_1 @ sk_D)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('132', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (m1_subset_1 @ 
% 0.36/0.55          (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55           X0) @ 
% 0.36/0.55          (k1_zfmisc_1 @ 
% 0.36/0.55           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['130', '131'])).
% 0.36/0.55  thf('133', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '45'])).
% 0.36/0.55  thf('134', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['34', '45'])).
% 0.36/0.55  thf('135', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (m1_subset_1 @ 
% 0.36/0.55          (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55           X0) @ 
% 0.36/0.55          (k1_zfmisc_1 @ 
% 0.36/0.55           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.36/0.55  thf('136', plain,
% 0.36/0.55      ((m1_subset_1 @ (k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('sup+', [status(thm)], ['127', '135'])).
% 0.36/0.55  thf(redefinition_r2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.36/0.55  thf('137', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.36/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.36/0.55          | ((X3) = (X6))
% 0.36/0.55          | ~ (r2_relset_1 @ X4 @ X5 @ X3 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.36/0.55  thf('138', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55             (k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) @ X0)
% 0.36/0.55          | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) = (X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ 
% 0.36/0.55               (k1_zfmisc_1 @ 
% 0.36/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.55      inference('sup-', [status(thm)], ['136', '137'])).
% 0.36/0.55  thf('139', plain,
% 0.36/0.55      ((~ (m1_subset_1 @ sk_D @ 
% 0.36/0.55           (k1_zfmisc_1 @ 
% 0.36/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.36/0.55        | ((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['126', '138'])).
% 0.36/0.55  thf('140', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D @ 
% 0.36/0.55        (k1_zfmisc_1 @ 
% 0.36/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '46'])).
% 0.36/0.55  thf('141', plain, (((k2_tmap_1 @ sk_C @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.36/0.55      inference('demod', [status(thm)], ['139', '140'])).
% 0.36/0.55  thf('142', plain,
% 0.36/0.55      (((sk_D)
% 0.36/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.36/0.55            (u1_struct_0 @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['115', '141'])).
% 0.36/0.55  thf('143', plain, (((sk_D) = (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.36/0.55      inference('sup+', [status(thm)], ['84', '142'])).
% 0.36/0.55  thf('144', plain,
% 0.36/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.36/0.55      inference('demod', [status(thm)], ['63', '143'])).
% 0.36/0.55  thf('145', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['60', '144'])).
% 0.36/0.55  thf(fc2_struct_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('146', plain,
% 0.36/0.55      (![X20 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 0.36/0.55          | ~ (l1_struct_0 @ X20)
% 0.36/0.55          | (v2_struct_0 @ X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.55  thf('147', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['145', '146'])).
% 0.36/0.55  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_l1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.55  thf('149', plain,
% 0.36/0.55      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('150', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['148', '149'])).
% 0.36/0.55  thf('151', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['147', '150'])).
% 0.36/0.55  thf('152', plain, ($false), inference('demod', [status(thm)], ['0', '151'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
