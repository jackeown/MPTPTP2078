%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ncBc5LmQy0

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:42 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 612 expanded)
%              Number of leaves         :   41 ( 191 expanded)
%              Depth                    :   20
%              Number of atoms          : 1289 (15348 expanded)
%              Number of equality atoms :   30 ( 257 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( m1_pre_topc @ X26 @ ( g1_pre_topc @ ( u1_struct_0 @ X25 ) @ ( u1_pre_topc @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) )
      | ( m1_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ~ ( m1_pre_topc @ X41 @ X43 )
      | ( r1_tarski @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ ( g1_pre_topc @ ( u1_struct_0 @ X24 ) @ ( u1_pre_topc @ X24 ) ) )
      | ( m1_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X40: $i] :
      ( ( m1_pre_topc @ X40 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ~ ( m1_pre_topc @ X41 @ X43 )
      | ( r1_tarski @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( m1_pre_topc @ X43 @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ( r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X27 @ X31 )
      | ( X27 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('66',plain,(
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

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('73',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k2_partfun1 @ X12 @ X13 @ X11 @ X14 )
        = ( k7_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','84'])).

thf('86',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('87',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('89',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('90',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('91',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3
        = ( k7_relat_1 @ X3 @ X4 ) )
      | ~ ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('94',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','45'])).

thf('98',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['87','98'])).

thf('100',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','99'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('101',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('104',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['0','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ncBc5LmQy0
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:27:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.72/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.72/0.91  % Solved by: fo/fo7.sh
% 0.72/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.91  % done 494 iterations in 0.456s
% 0.72/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.72/0.91  % SZS output start Refutation
% 0.72/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.72/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.72/0.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.72/0.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.72/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.72/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.91  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.72/0.91  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.72/0.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.72/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.91  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.72/0.91  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.72/0.91  thf(sk_D_type, type, sk_D: $i).
% 0.72/0.91  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.72/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.91  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.72/0.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.72/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.91  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.72/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.72/0.91  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.72/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.72/0.91  thf(t60_tmap_1, conjecture,
% 0.72/0.91    (![A:$i]:
% 0.72/0.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.72/0.91       ( ![B:$i]:
% 0.72/0.91         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.72/0.91             ( l1_pre_topc @ B ) ) =>
% 0.72/0.91           ( ![C:$i]:
% 0.72/0.91             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.72/0.91               ( ![D:$i]:
% 0.72/0.91                 ( ( ( v1_funct_1 @ D ) & 
% 0.72/0.91                     ( v1_funct_2 @
% 0.72/0.91                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.72/0.91                     ( m1_subset_1 @
% 0.72/0.91                       D @ 
% 0.72/0.91                       ( k1_zfmisc_1 @
% 0.72/0.91                         ( k2_zfmisc_1 @
% 0.72/0.91                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.72/0.91                   ( ( ( g1_pre_topc @
% 0.72/0.91                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.72/0.91                       ( g1_pre_topc @
% 0.72/0.91                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.72/0.91                     ( r1_funct_2 @
% 0.72/0.91                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.72/0.91                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.72/0.91                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.72/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.91    (~( ![A:$i]:
% 0.72/0.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.72/0.91            ( l1_pre_topc @ A ) ) =>
% 0.72/0.91          ( ![B:$i]:
% 0.72/0.91            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.72/0.91                ( l1_pre_topc @ B ) ) =>
% 0.72/0.91              ( ![C:$i]:
% 0.72/0.91                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.72/0.91                  ( ![D:$i]:
% 0.72/0.91                    ( ( ( v1_funct_1 @ D ) & 
% 0.72/0.91                        ( v1_funct_2 @
% 0.72/0.91                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.72/0.91                        ( m1_subset_1 @
% 0.72/0.91                          D @ 
% 0.72/0.91                          ( k1_zfmisc_1 @
% 0.72/0.91                            ( k2_zfmisc_1 @
% 0.72/0.91                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.72/0.91                      ( ( ( g1_pre_topc @
% 0.72/0.91                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.72/0.91                          ( g1_pre_topc @
% 0.72/0.91                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.72/0.91                        ( r1_funct_2 @
% 0.72/0.91                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.72/0.91                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.72/0.91                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.72/0.91    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.72/0.91  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('1', plain,
% 0.72/0.91      ((m1_subset_1 @ sk_D @ 
% 0.72/0.91        (k1_zfmisc_1 @ 
% 0.72/0.91         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf('3', plain,
% 0.72/0.91      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.72/0.91         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.72/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.91  thf(t2_tsep_1, axiom,
% 0.72/0.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.72/0.91  thf('4', plain,
% 0.72/0.91      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 0.72/0.91      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.72/0.91  thf(t65_pre_topc, axiom,
% 0.72/0.91    (![A:$i]:
% 0.72/0.91     ( ( l1_pre_topc @ A ) =>
% 0.72/0.91       ( ![B:$i]:
% 0.72/0.91         ( ( l1_pre_topc @ B ) =>
% 0.72/0.91           ( ( m1_pre_topc @ A @ B ) <=>
% 0.72/0.91             ( m1_pre_topc @
% 0.72/0.91               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.72/0.91  thf('5', plain,
% 0.72/0.91      (![X25 : $i, X26 : $i]:
% 0.72/0.91         (~ (l1_pre_topc @ X25)
% 0.72/0.91          | ~ (m1_pre_topc @ X26 @ X25)
% 0.72/0.91          | (m1_pre_topc @ X26 @ 
% 0.72/0.91             (g1_pre_topc @ (u1_struct_0 @ X25) @ (u1_pre_topc @ X25)))
% 0.72/0.91          | ~ (l1_pre_topc @ X26))),
% 0.72/0.91      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.72/0.91  thf('6', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         (~ (l1_pre_topc @ X0)
% 0.72/0.91          | ~ (l1_pre_topc @ X0)
% 0.72/0.91          | (m1_pre_topc @ X0 @ 
% 0.72/0.91             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.72/0.91          | ~ (l1_pre_topc @ X0))),
% 0.72/0.91      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.91  thf('7', plain,
% 0.72/0.91      (![X0 : $i]:
% 0.72/0.91         ((m1_pre_topc @ X0 @ 
% 0.72/0.91           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.72/0.91          | ~ (l1_pre_topc @ X0))),
% 0.72/0.91      inference('simplify', [status(thm)], ['6'])).
% 0.72/0.91  thf('8', plain,
% 0.72/0.91      (((m1_pre_topc @ sk_B @ 
% 0.72/0.91         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.72/0.91        | ~ (l1_pre_topc @ sk_B))),
% 0.72/0.92      inference('sup+', [status(thm)], ['3', '7'])).
% 0.72/0.92  thf('9', plain, ((l1_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('10', plain,
% 0.72/0.92      ((m1_pre_topc @ sk_B @ 
% 0.72/0.92        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.72/0.92      inference('demod', [status(thm)], ['8', '9'])).
% 0.72/0.92  thf('11', plain,
% 0.72/0.92      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.72/0.92         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(t59_pre_topc, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( l1_pre_topc @ A ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( m1_pre_topc @
% 0.72/0.92             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.72/0.92           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.72/0.92  thf('12', plain,
% 0.72/0.92      (![X23 : $i, X24 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X23 @ 
% 0.72/0.92             (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)))
% 0.72/0.92          | (m1_pre_topc @ X23 @ X24)
% 0.72/0.92          | ~ (l1_pre_topc @ X24))),
% 0.72/0.92      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.72/0.92  thf('13', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X0 @ 
% 0.72/0.92             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.72/0.92          | ~ (l1_pre_topc @ sk_B)
% 0.72/0.92          | (m1_pre_topc @ X0 @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['11', '12'])).
% 0.72/0.92  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('15', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X0 @ 
% 0.72/0.92             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.72/0.92          | (m1_pre_topc @ X0 @ sk_B))),
% 0.72/0.92      inference('demod', [status(thm)], ['13', '14'])).
% 0.72/0.92  thf('16', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.72/0.92      inference('sup-', [status(thm)], ['10', '15'])).
% 0.72/0.92  thf(t4_tsep_1, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( m1_pre_topc @ B @ A ) =>
% 0.72/0.92           ( ![C:$i]:
% 0.72/0.92             ( ( m1_pre_topc @ C @ A ) =>
% 0.72/0.92               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.72/0.92                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.72/0.92  thf('17', plain,
% 0.72/0.92      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X41 @ X42)
% 0.72/0.92          | ~ (m1_pre_topc @ X41 @ X43)
% 0.72/0.92          | (r1_tarski @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X43))
% 0.72/0.92          | ~ (m1_pre_topc @ X43 @ X42)
% 0.72/0.92          | ~ (l1_pre_topc @ X42)
% 0.72/0.92          | ~ (v2_pre_topc @ X42))),
% 0.72/0.92      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.72/0.92  thf('18', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (v2_pre_topc @ sk_B)
% 0.72/0.92          | ~ (l1_pre_topc @ sk_B)
% 0.72/0.92          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.72/0.92          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.72/0.92          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['16', '17'])).
% 0.72/0.92  thf('19', plain, ((v2_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('20', plain, ((l1_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('21', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.72/0.92          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.72/0.92          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.72/0.92      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.72/0.92  thf('22', plain,
% 0.72/0.92      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.72/0.92        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['2', '21'])).
% 0.72/0.92  thf('23', plain,
% 0.72/0.92      ((m1_pre_topc @ sk_B @ 
% 0.72/0.92        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.72/0.92      inference('demod', [status(thm)], ['8', '9'])).
% 0.72/0.92  thf('24', plain,
% 0.72/0.92      (![X23 : $i, X24 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X23 @ 
% 0.72/0.92             (g1_pre_topc @ (u1_struct_0 @ X24) @ (u1_pre_topc @ X24)))
% 0.72/0.92          | (m1_pre_topc @ X23 @ X24)
% 0.72/0.92          | ~ (l1_pre_topc @ X24))),
% 0.72/0.92      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.72/0.92  thf('25', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.72/0.92      inference('sup-', [status(thm)], ['23', '24'])).
% 0.72/0.92  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(dt_m1_pre_topc, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( l1_pre_topc @ A ) =>
% 0.72/0.92       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.72/0.92  thf('27', plain,
% 0.72/0.92      (![X18 : $i, X19 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X18 @ X19)
% 0.72/0.92          | (l1_pre_topc @ X18)
% 0.72/0.92          | ~ (l1_pre_topc @ X19))),
% 0.72/0.92      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.72/0.92  thf('28', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.72/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.72/0.92  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('30', plain, ((l1_pre_topc @ sk_C)),
% 0.72/0.92      inference('demod', [status(thm)], ['28', '29'])).
% 0.72/0.92  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.72/0.92      inference('demod', [status(thm)], ['25', '30'])).
% 0.72/0.92  thf('32', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.72/0.92      inference('demod', [status(thm)], ['22', '31'])).
% 0.72/0.92  thf(d10_xboole_0, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.92  thf('33', plain,
% 0.72/0.92      (![X0 : $i, X2 : $i]:
% 0.72/0.92         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.72/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.92  thf('34', plain,
% 0.72/0.92      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.72/0.92        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['32', '33'])).
% 0.72/0.92  thf('35', plain,
% 0.72/0.92      (![X40 : $i]: ((m1_pre_topc @ X40 @ X40) | ~ (l1_pre_topc @ X40))),
% 0.72/0.92      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.72/0.92  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('37', plain,
% 0.72/0.92      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X41 @ X42)
% 0.72/0.92          | ~ (m1_pre_topc @ X41 @ X43)
% 0.72/0.92          | (r1_tarski @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X43))
% 0.72/0.92          | ~ (m1_pre_topc @ X43 @ X42)
% 0.72/0.92          | ~ (l1_pre_topc @ X42)
% 0.72/0.92          | ~ (v2_pre_topc @ X42))),
% 0.72/0.92      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.72/0.92  thf('38', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (v2_pre_topc @ sk_B)
% 0.72/0.92          | ~ (l1_pre_topc @ sk_B)
% 0.72/0.92          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.72/0.92          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.72/0.92          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['36', '37'])).
% 0.72/0.92  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('41', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (~ (m1_pre_topc @ X0 @ sk_B)
% 0.72/0.92          | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.72/0.92          | ~ (m1_pre_topc @ sk_C @ X0))),
% 0.72/0.92      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.72/0.92  thf('42', plain,
% 0.72/0.92      ((~ (l1_pre_topc @ sk_B)
% 0.72/0.92        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.72/0.92        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['35', '41'])).
% 0.72/0.92  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('44', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('45', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.72/0.92      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.72/0.92  thf('46', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.72/0.92      inference('demod', [status(thm)], ['34', '45'])).
% 0.72/0.92  thf('47', plain,
% 0.72/0.92      ((m1_subset_1 @ sk_D @ 
% 0.72/0.92        (k1_zfmisc_1 @ 
% 0.72/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.72/0.92      inference('demod', [status(thm)], ['1', '46'])).
% 0.72/0.92  thf('48', plain,
% 0.72/0.92      ((m1_subset_1 @ sk_D @ 
% 0.72/0.92        (k1_zfmisc_1 @ 
% 0.72/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(redefinition_r1_funct_2, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.72/0.92     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.72/0.92         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.72/0.92         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.72/0.92         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.72/0.92         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.72/0.92       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.72/0.92  thf('49', plain,
% 0.72/0.92      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.72/0.92          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.72/0.92          | ~ (v1_funct_1 @ X27)
% 0.72/0.92          | (v1_xboole_0 @ X30)
% 0.72/0.92          | (v1_xboole_0 @ X29)
% 0.72/0.92          | ~ (v1_funct_1 @ X31)
% 0.72/0.92          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 0.72/0.92          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.72/0.92          | (r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X27 @ X31)
% 0.72/0.92          | ((X27) != (X31)))),
% 0.72/0.92      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.72/0.92  thf('50', plain,
% 0.72/0.92      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.72/0.92         ((r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X31 @ X31)
% 0.72/0.92          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.72/0.92          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 0.72/0.92          | (v1_xboole_0 @ X29)
% 0.72/0.92          | (v1_xboole_0 @ X30)
% 0.72/0.92          | ~ (v1_funct_1 @ X31)
% 0.72/0.92          | ~ (v1_funct_2 @ X31 @ X28 @ X29)
% 0.72/0.92          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.72/0.92      inference('simplify', [status(thm)], ['49'])).
% 0.72/0.92  thf('51', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.72/0.92          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.72/0.92          | ~ (v1_funct_1 @ sk_D)
% 0.72/0.92          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.72/0.92          | (v1_xboole_0 @ X0)
% 0.72/0.92          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.72/0.92          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.72/0.92             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.72/0.92      inference('sup-', [status(thm)], ['48', '50'])).
% 0.72/0.92  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('53', plain,
% 0.72/0.92      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('54', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.72/0.92          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.72/0.92          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.72/0.92          | (v1_xboole_0 @ X0)
% 0.72/0.92          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.72/0.92             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.72/0.92      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.72/0.92  thf('55', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.72/0.92      inference('demod', [status(thm)], ['34', '45'])).
% 0.72/0.92  thf('56', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.72/0.92          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.72/0.92          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.72/0.92          | (v1_xboole_0 @ X0)
% 0.72/0.92          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.72/0.92             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.72/0.92      inference('demod', [status(thm)], ['54', '55'])).
% 0.72/0.92  thf('57', plain,
% 0.72/0.92      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.72/0.92        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['47', '56'])).
% 0.72/0.92  thf('58', plain,
% 0.72/0.92      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('59', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.72/0.92      inference('demod', [status(thm)], ['34', '45'])).
% 0.72/0.92  thf('60', plain,
% 0.72/0.92      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('demod', [status(thm)], ['58', '59'])).
% 0.72/0.92  thf('61', plain,
% 0.72/0.92      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.72/0.92        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.72/0.92      inference('demod', [status(thm)], ['57', '60'])).
% 0.72/0.92  thf('62', plain,
% 0.72/0.92      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.72/0.92        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.72/0.92      inference('simplify', [status(thm)], ['61'])).
% 0.72/0.92  thf('63', plain,
% 0.72/0.92      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.72/0.92          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('64', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('65', plain,
% 0.72/0.92      ((m1_subset_1 @ sk_D @ 
% 0.72/0.92        (k1_zfmisc_1 @ 
% 0.72/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(d4_tmap_1, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.72/0.92             ( l1_pre_topc @ B ) ) =>
% 0.72/0.92           ( ![C:$i]:
% 0.72/0.92             ( ( ( v1_funct_1 @ C ) & 
% 0.72/0.92                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.72/0.92                 ( m1_subset_1 @
% 0.72/0.92                   C @ 
% 0.72/0.92                   ( k1_zfmisc_1 @
% 0.72/0.92                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.72/0.92               ( ![D:$i]:
% 0.72/0.92                 ( ( m1_pre_topc @ D @ A ) =>
% 0.72/0.92                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.72/0.92                     ( k2_partfun1 @
% 0.72/0.92                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.72/0.92                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.72/0.92  thf('66', plain,
% 0.72/0.92      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.72/0.92         ((v2_struct_0 @ X33)
% 0.72/0.92          | ~ (v2_pre_topc @ X33)
% 0.72/0.92          | ~ (l1_pre_topc @ X33)
% 0.72/0.92          | ~ (m1_pre_topc @ X34 @ X35)
% 0.72/0.92          | ((k2_tmap_1 @ X35 @ X33 @ X36 @ X34)
% 0.72/0.92              = (k2_partfun1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33) @ 
% 0.72/0.92                 X36 @ (u1_struct_0 @ X34)))
% 0.72/0.92          | ~ (m1_subset_1 @ X36 @ 
% 0.72/0.92               (k1_zfmisc_1 @ 
% 0.72/0.92                (k2_zfmisc_1 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))))
% 0.72/0.92          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X33))
% 0.72/0.92          | ~ (v1_funct_1 @ X36)
% 0.72/0.92          | ~ (l1_pre_topc @ X35)
% 0.72/0.92          | ~ (v2_pre_topc @ X35)
% 0.72/0.92          | (v2_struct_0 @ X35))),
% 0.72/0.92      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.72/0.92  thf('67', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((v2_struct_0 @ sk_B)
% 0.72/0.92          | ~ (v2_pre_topc @ sk_B)
% 0.72/0.92          | ~ (l1_pre_topc @ sk_B)
% 0.72/0.92          | ~ (v1_funct_1 @ sk_D)
% 0.72/0.92          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.72/0.92          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.72/0.92              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92                 sk_D @ (u1_struct_0 @ X0)))
% 0.72/0.92          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.72/0.92          | ~ (l1_pre_topc @ sk_A)
% 0.72/0.92          | ~ (v2_pre_topc @ sk_A)
% 0.72/0.92          | (v2_struct_0 @ sk_A))),
% 0.72/0.92      inference('sup-', [status(thm)], ['65', '66'])).
% 0.72/0.92  thf('68', plain, ((v2_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('71', plain,
% 0.72/0.92      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('72', plain,
% 0.72/0.92      ((m1_subset_1 @ sk_D @ 
% 0.72/0.92        (k1_zfmisc_1 @ 
% 0.72/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(redefinition_k2_partfun1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.92     ( ( ( v1_funct_1 @ C ) & 
% 0.72/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.72/0.92       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.72/0.92  thf('73', plain,
% 0.72/0.92      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.72/0.92         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.72/0.92          | ~ (v1_funct_1 @ X11)
% 0.72/0.92          | ((k2_partfun1 @ X12 @ X13 @ X11 @ X14) = (k7_relat_1 @ X11 @ X14)))),
% 0.72/0.92      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.72/0.92  thf('74', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.72/0.92            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.72/0.92          | ~ (v1_funct_1 @ sk_D))),
% 0.72/0.92      inference('sup-', [status(thm)], ['72', '73'])).
% 0.72/0.92  thf('75', plain, ((v1_funct_1 @ sk_D)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('76', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.72/0.92           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.72/0.92      inference('demod', [status(thm)], ['74', '75'])).
% 0.72/0.92  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('79', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((v2_struct_0 @ sk_B)
% 0.72/0.92          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.72/0.92              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.72/0.92          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.72/0.92          | (v2_struct_0 @ sk_A))),
% 0.72/0.92      inference('demod', [status(thm)],
% 0.72/0.92                ['67', '68', '69', '70', '71', '76', '77', '78'])).
% 0.72/0.92  thf('80', plain,
% 0.72/0.92      (((v2_struct_0 @ sk_A)
% 0.72/0.92        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.72/0.92            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.72/0.92        | (v2_struct_0 @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['64', '79'])).
% 0.72/0.92  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('82', plain,
% 0.72/0.92      (((v2_struct_0 @ sk_B)
% 0.72/0.92        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.72/0.92            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.72/0.92      inference('clc', [status(thm)], ['80', '81'])).
% 0.72/0.92  thf('83', plain, (~ (v2_struct_0 @ sk_B)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('84', plain,
% 0.72/0.92      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.72/0.92         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.72/0.92      inference('clc', [status(thm)], ['82', '83'])).
% 0.72/0.92  thf('85', plain,
% 0.72/0.92      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.72/0.92          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.72/0.92      inference('demod', [status(thm)], ['63', '84'])).
% 0.72/0.92  thf('86', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.72/0.92      inference('demod', [status(thm)], ['34', '45'])).
% 0.72/0.92  thf('87', plain,
% 0.72/0.92      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.72/0.92          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.72/0.92      inference('demod', [status(thm)], ['85', '86'])).
% 0.72/0.92  thf('88', plain,
% 0.72/0.92      ((m1_subset_1 @ sk_D @ 
% 0.72/0.92        (k1_zfmisc_1 @ 
% 0.72/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(cc2_relset_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.72/0.92  thf('89', plain,
% 0.72/0.92      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.72/0.92         ((v4_relat_1 @ X8 @ X9)
% 0.72/0.92          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.72/0.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.72/0.92  thf('90', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.72/0.92      inference('sup-', [status(thm)], ['88', '89'])).
% 0.72/0.92  thf(t209_relat_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.72/0.92       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.72/0.92  thf('91', plain,
% 0.72/0.92      (![X3 : $i, X4 : $i]:
% 0.72/0.92         (((X3) = (k7_relat_1 @ X3 @ X4))
% 0.72/0.92          | ~ (v4_relat_1 @ X3 @ X4)
% 0.72/0.92          | ~ (v1_relat_1 @ X3))),
% 0.72/0.92      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.72/0.92  thf('92', plain,
% 0.72/0.92      ((~ (v1_relat_1 @ sk_D)
% 0.72/0.92        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['90', '91'])).
% 0.72/0.92  thf('93', plain,
% 0.72/0.92      ((m1_subset_1 @ sk_D @ 
% 0.72/0.92        (k1_zfmisc_1 @ 
% 0.72/0.92         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(cc1_relset_1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.92       ( v1_relat_1 @ C ) ))).
% 0.72/0.92  thf('94', plain,
% 0.72/0.92      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.72/0.92         ((v1_relat_1 @ X5)
% 0.72/0.92          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.72/0.92      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.72/0.92  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 0.72/0.92      inference('sup-', [status(thm)], ['93', '94'])).
% 0.72/0.92  thf('96', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.72/0.92      inference('demod', [status(thm)], ['92', '95'])).
% 0.72/0.92  thf('97', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.72/0.92      inference('demod', [status(thm)], ['34', '45'])).
% 0.72/0.92  thf('98', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.72/0.92      inference('demod', [status(thm)], ['96', '97'])).
% 0.72/0.92  thf('99', plain,
% 0.72/0.92      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.72/0.92          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.72/0.92      inference('demod', [status(thm)], ['87', '98'])).
% 0.72/0.92  thf('100', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.72/0.92      inference('clc', [status(thm)], ['62', '99'])).
% 0.72/0.92  thf(fc2_struct_0, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.72/0.92       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.72/0.92  thf('101', plain,
% 0.72/0.92      (![X21 : $i]:
% 0.72/0.92         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.72/0.92          | ~ (l1_struct_0 @ X21)
% 0.72/0.92          | (v2_struct_0 @ X21))),
% 0.72/0.92      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.72/0.92  thf('102', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.72/0.92      inference('sup-', [status(thm)], ['100', '101'])).
% 0.72/0.92  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(dt_l1_pre_topc, axiom,
% 0.72/0.92    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.72/0.92  thf('104', plain,
% 0.72/0.92      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.72/0.92      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.72/0.92  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 0.72/0.92      inference('sup-', [status(thm)], ['103', '104'])).
% 0.72/0.92  thf('106', plain, ((v2_struct_0 @ sk_A)),
% 0.72/0.92      inference('demod', [status(thm)], ['102', '105'])).
% 0.72/0.92  thf('107', plain, ($false), inference('demod', [status(thm)], ['0', '106'])).
% 0.72/0.92  
% 0.72/0.92  % SZS output end Refutation
% 0.72/0.92  
% 0.72/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
