%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xnv2w7uWdy

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:44 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 904 expanded)
%              Number of leaves         :   45 ( 278 expanded)
%              Depth                    :   24
%              Number of atoms          : 1299 (18806 expanded)
%              Number of equality atoms :   36 ( 320 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X39 @ X40 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ! [X41: $i] :
      ( ( m1_pre_topc @ X41 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( m1_pre_topc @ X28 @ ( g1_pre_topc @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ( m1_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_pre_topc @ X39 @ X40 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ( r1_funct_2 @ X30 @ X31 @ X34 @ X32 @ X29 @ X33 )
      | ( X29 != X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('37',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r1_funct_2 @ X30 @ X31 @ X34 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X32 )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_pre_topc @ X36 @ X37 )
      | ( ( k2_tmap_1 @ X37 @ X35 @ X38 @ X36 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) @ X38 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) ) ) )
      | ~ ( v1_funct_2 @ X38 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X35 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ( ( k2_partfun1 @ X18 @ X19 @ X17 @ X20 )
        = ( k7_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63','70','71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('77',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('78',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('83',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','84'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['82','83'])).

thf('89',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    = sk_D ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','32'])).

thf('91',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['50','96'])).

thf('98',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','97'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('99',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('102',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xnv2w7uWdy
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:06:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 197 iterations in 0.126s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.41/0.58  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.41/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.41/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.41/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.58  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.41/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.58  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.41/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.58  thf(t60_tmap_1, conjecture,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.58             ( l1_pre_topc @ B ) ) =>
% 0.41/0.58           ( ![C:$i]:
% 0.41/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.41/0.58               ( ![D:$i]:
% 0.41/0.58                 ( ( ( v1_funct_1 @ D ) & 
% 0.41/0.58                     ( v1_funct_2 @
% 0.41/0.58                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.58                     ( m1_subset_1 @
% 0.41/0.58                       D @ 
% 0.41/0.58                       ( k1_zfmisc_1 @
% 0.41/0.58                         ( k2_zfmisc_1 @
% 0.41/0.58                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.58                   ( ( ( g1_pre_topc @
% 0.41/0.58                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.41/0.58                       ( g1_pre_topc @
% 0.41/0.58                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.41/0.58                     ( r1_funct_2 @
% 0.41/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.58                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.41/0.58                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i]:
% 0.41/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.58            ( l1_pre_topc @ A ) ) =>
% 0.41/0.58          ( ![B:$i]:
% 0.41/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.58                ( l1_pre_topc @ B ) ) =>
% 0.41/0.58              ( ![C:$i]:
% 0.41/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.41/0.58                  ( ![D:$i]:
% 0.41/0.58                    ( ( ( v1_funct_1 @ D ) & 
% 0.41/0.58                        ( v1_funct_2 @
% 0.41/0.58                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.41/0.58                        ( m1_subset_1 @
% 0.41/0.58                          D @ 
% 0.41/0.58                          ( k1_zfmisc_1 @
% 0.41/0.58                            ( k2_zfmisc_1 @
% 0.41/0.58                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.41/0.58                      ( ( ( g1_pre_topc @
% 0.41/0.58                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.41/0.58                          ( g1_pre_topc @
% 0.41/0.58                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.41/0.58                        ( r1_funct_2 @
% 0.41/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.58                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.41/0.58                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.41/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_D @ 
% 0.41/0.58        (k1_zfmisc_1 @ 
% 0.41/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(t1_tsep_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( l1_pre_topc @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.58           ( m1_subset_1 @
% 0.41/0.58             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (![X39 : $i, X40 : $i]:
% 0.41/0.58         (~ (m1_pre_topc @ X39 @ X40)
% 0.41/0.58          | (m1_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.41/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.41/0.58          | ~ (l1_pre_topc @ X40))),
% 0.41/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.41/0.58        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.41/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.58  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.41/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.41/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.58  thf(t3_subset, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (![X3 : $i, X4 : $i]:
% 0.41/0.58         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.58  thf('8', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.58  thf(d10_xboole_0, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      (![X0 : $i, X2 : $i]:
% 0.41/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.41/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.41/0.58        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.41/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(t2_tsep_1, axiom,
% 0.41/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.41/0.58  thf('12', plain,
% 0.41/0.58      (![X41 : $i]: ((m1_pre_topc @ X41 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.41/0.58      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.41/0.58  thf(t65_pre_topc, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( l1_pre_topc @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( l1_pre_topc @ B ) =>
% 0.41/0.58           ( ( m1_pre_topc @ A @ B ) <=>
% 0.41/0.58             ( m1_pre_topc @
% 0.41/0.58               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (![X27 : $i, X28 : $i]:
% 0.41/0.58         (~ (l1_pre_topc @ X27)
% 0.41/0.58          | ~ (m1_pre_topc @ X28 @ X27)
% 0.41/0.58          | (m1_pre_topc @ X28 @ 
% 0.41/0.58             (g1_pre_topc @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27)))
% 0.41/0.58          | ~ (l1_pre_topc @ X28))),
% 0.41/0.58      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (~ (l1_pre_topc @ X0)
% 0.41/0.58          | ~ (l1_pre_topc @ X0)
% 0.41/0.58          | (m1_pre_topc @ X0 @ 
% 0.41/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.58          | ~ (l1_pre_topc @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.58  thf('15', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((m1_pre_topc @ X0 @ 
% 0.41/0.58           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.41/0.58          | ~ (l1_pre_topc @ X0))),
% 0.41/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      (((m1_pre_topc @ sk_B @ 
% 0.41/0.58         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.41/0.58        | ~ (l1_pre_topc @ sk_B))),
% 0.41/0.58      inference('sup+', [status(thm)], ['11', '15'])).
% 0.41/0.58  thf('17', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      ((m1_pre_topc @ sk_B @ 
% 0.41/0.58        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.41/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf(t59_pre_topc, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( l1_pre_topc @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_pre_topc @
% 0.41/0.58             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.41/0.58           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      (![X25 : $i, X26 : $i]:
% 0.41/0.58         (~ (m1_pre_topc @ X25 @ 
% 0.41/0.58             (g1_pre_topc @ (u1_struct_0 @ X26) @ (u1_pre_topc @ X26)))
% 0.41/0.58          | (m1_pre_topc @ X25 @ X26)
% 0.41/0.58          | ~ (l1_pre_topc @ X26))),
% 0.41/0.58      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.41/0.58  thf('20', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.41/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.58  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(dt_m1_pre_topc, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( l1_pre_topc @ A ) =>
% 0.41/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      (![X22 : $i, X23 : $i]:
% 0.41/0.58         (~ (m1_pre_topc @ X22 @ X23)
% 0.41/0.58          | (l1_pre_topc @ X22)
% 0.41/0.58          | ~ (l1_pre_topc @ X23))),
% 0.41/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.58  thf('23', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.41/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.58  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('25', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.58  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.41/0.58      inference('demod', [status(thm)], ['20', '25'])).
% 0.41/0.58  thf('27', plain,
% 0.41/0.58      (![X39 : $i, X40 : $i]:
% 0.41/0.58         (~ (m1_pre_topc @ X39 @ X40)
% 0.41/0.58          | (m1_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.41/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.41/0.58          | ~ (l1_pre_topc @ X40))),
% 0.41/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      ((~ (l1_pre_topc @ sk_C)
% 0.41/0.58        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.58  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.41/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.58  thf('30', plain,
% 0.41/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.41/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.41/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.41/0.58  thf('31', plain,
% 0.41/0.58      (![X3 : $i, X4 : $i]:
% 0.41/0.58         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.58  thf('32', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.58  thf('33', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_D @ 
% 0.41/0.58        (k1_zfmisc_1 @ 
% 0.41/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.58      inference('demod', [status(thm)], ['1', '33'])).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_D @ 
% 0.41/0.58        (k1_zfmisc_1 @ 
% 0.41/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.58      inference('demod', [status(thm)], ['1', '33'])).
% 0.41/0.58  thf(redefinition_r1_funct_2, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.58     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.41/0.58         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.41/0.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.58         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.41/0.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.41/0.58       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.41/0.58          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.41/0.58          | ~ (v1_funct_1 @ X29)
% 0.41/0.58          | (v1_xboole_0 @ X32)
% 0.41/0.58          | (v1_xboole_0 @ X31)
% 0.41/0.58          | ~ (v1_funct_1 @ X33)
% 0.41/0.58          | ~ (v1_funct_2 @ X33 @ X34 @ X32)
% 0.41/0.58          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.41/0.58          | (r1_funct_2 @ X30 @ X31 @ X34 @ X32 @ X29 @ X33)
% 0.41/0.58          | ((X29) != (X33)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.58         ((r1_funct_2 @ X30 @ X31 @ X34 @ X32 @ X33 @ X33)
% 0.41/0.58          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 0.41/0.58          | ~ (v1_funct_2 @ X33 @ X34 @ X32)
% 0.41/0.58          | (v1_xboole_0 @ X31)
% 0.41/0.58          | (v1_xboole_0 @ X32)
% 0.41/0.58          | ~ (v1_funct_1 @ X33)
% 0.41/0.58          | ~ (v1_funct_2 @ X33 @ X30 @ X31)
% 0.41/0.58          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.41/0.58      inference('simplify', [status(thm)], ['36'])).
% 0.41/0.58  thf('38', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.41/0.58          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.41/0.58          | ~ (v1_funct_1 @ sk_D)
% 0.41/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.58          | (v1_xboole_0 @ X0)
% 0.41/0.58          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.41/0.58          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.41/0.58             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.41/0.58      inference('sup-', [status(thm)], ['35', '37'])).
% 0.41/0.58  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('40', plain,
% 0.41/0.58      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('41', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.58  thf('42', plain,
% 0.41/0.58      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.41/0.58  thf('43', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.41/0.58          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.41/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.58          | (v1_xboole_0 @ X0)
% 0.41/0.58          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.41/0.58             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.41/0.58      inference('demod', [status(thm)], ['38', '39', '42'])).
% 0.41/0.58  thf('44', plain,
% 0.41/0.58      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.58         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.41/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.58        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['34', '43'])).
% 0.41/0.58  thf('45', plain,
% 0.41/0.58      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.41/0.58  thf('46', plain,
% 0.41/0.58      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.58         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.41/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['44', '45'])).
% 0.41/0.58  thf('47', plain,
% 0.41/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.58        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.58           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.41/0.58      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.58  thf('48', plain,
% 0.41/0.58      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.58          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.41/0.58          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('49', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.58  thf('50', plain,
% 0.41/0.58      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.58          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.41/0.58          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.41/0.58  thf('51', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('52', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_D @ 
% 0.41/0.58        (k1_zfmisc_1 @ 
% 0.41/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.58      inference('demod', [status(thm)], ['1', '33'])).
% 0.41/0.58  thf('53', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.58  thf(d4_tmap_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.41/0.58             ( l1_pre_topc @ B ) ) =>
% 0.41/0.58           ( ![C:$i]:
% 0.41/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.58                 ( m1_subset_1 @
% 0.41/0.58                   C @ 
% 0.41/0.58                   ( k1_zfmisc_1 @
% 0.41/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.58               ( ![D:$i]:
% 0.41/0.58                 ( ( m1_pre_topc @ D @ A ) =>
% 0.41/0.58                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.41/0.58                     ( k2_partfun1 @
% 0.41/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.41/0.58                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.58  thf('54', plain,
% 0.41/0.58      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.41/0.58         ((v2_struct_0 @ X35)
% 0.41/0.58          | ~ (v2_pre_topc @ X35)
% 0.41/0.58          | ~ (l1_pre_topc @ X35)
% 0.41/0.58          | ~ (m1_pre_topc @ X36 @ X37)
% 0.41/0.58          | ((k2_tmap_1 @ X37 @ X35 @ X38 @ X36)
% 0.41/0.58              = (k2_partfun1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35) @ 
% 0.41/0.58                 X38 @ (u1_struct_0 @ X36)))
% 0.41/0.58          | ~ (m1_subset_1 @ X38 @ 
% 0.41/0.58               (k1_zfmisc_1 @ 
% 0.41/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))))
% 0.41/0.58          | ~ (v1_funct_2 @ X38 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X35))
% 0.41/0.58          | ~ (v1_funct_1 @ X38)
% 0.41/0.58          | ~ (l1_pre_topc @ X37)
% 0.41/0.58          | ~ (v2_pre_topc @ X37)
% 0.41/0.58          | (v2_struct_0 @ X37))),
% 0.41/0.58      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.41/0.58  thf('55', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X1 @ 
% 0.41/0.58             (k1_zfmisc_1 @ 
% 0.41/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.41/0.58          | (v2_struct_0 @ sk_B)
% 0.41/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.41/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.41/0.58          | ~ (v1_funct_1 @ X1)
% 0.41/0.58          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.41/0.58          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.41/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.41/0.58                 X1 @ (u1_struct_0 @ X2)))
% 0.41/0.58          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.41/0.58          | ~ (l1_pre_topc @ X0)
% 0.41/0.58          | ~ (v2_pre_topc @ X0)
% 0.41/0.58          | (v2_struct_0 @ X0))),
% 0.41/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.58  thf('56', plain, ((v2_pre_topc @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('58', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.58  thf('59', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.58  thf('60', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X1 @ 
% 0.41/0.58             (k1_zfmisc_1 @ 
% 0.41/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.41/0.58          | (v2_struct_0 @ sk_B)
% 0.41/0.58          | ~ (v1_funct_1 @ X1)
% 0.41/0.58          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.41/0.58          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.41/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.41/0.58                 X1 @ (u1_struct_0 @ X2)))
% 0.41/0.58          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.41/0.58          | ~ (l1_pre_topc @ X0)
% 0.41/0.58          | ~ (v2_pre_topc @ X0)
% 0.41/0.58          | (v2_struct_0 @ X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.41/0.58  thf('61', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((v2_struct_0 @ sk_A)
% 0.41/0.58          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.58          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.58          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.58          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.41/0.58              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.58                 sk_D @ (u1_struct_0 @ X0)))
% 0.41/0.58          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.41/0.58          | ~ (v1_funct_1 @ sk_D)
% 0.41/0.58          | (v2_struct_0 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['52', '60'])).
% 0.41/0.58  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('64', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_D @ 
% 0.41/0.58        (k1_zfmisc_1 @ 
% 0.41/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k2_partfun1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.58     ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.58       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.41/0.58  thf('65', plain,
% 0.41/0.58      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.41/0.58          | ~ (v1_funct_1 @ X17)
% 0.41/0.58          | ((k2_partfun1 @ X18 @ X19 @ X17 @ X20) = (k7_relat_1 @ X17 @ X20)))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.41/0.58  thf('66', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.41/0.58            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.41/0.58          | ~ (v1_funct_1 @ sk_D))),
% 0.41/0.58      inference('sup-', [status(thm)], ['64', '65'])).
% 0.41/0.58  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('68', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.41/0.58           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['66', '67'])).
% 0.41/0.58  thf('69', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.58  thf('70', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.41/0.58           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['68', '69'])).
% 0.41/0.58  thf('71', plain,
% 0.41/0.58      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.41/0.58  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('73', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((v2_struct_0 @ sk_A)
% 0.41/0.58          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.41/0.58          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.41/0.58              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.41/0.58          | (v2_struct_0 @ sk_B))),
% 0.41/0.58      inference('demod', [status(thm)], ['61', '62', '63', '70', '71', '72'])).
% 0.41/0.58  thf('74', plain,
% 0.41/0.58      (((v2_struct_0 @ sk_B)
% 0.41/0.58        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.41/0.58            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.41/0.58        | (v2_struct_0 @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['51', '73'])).
% 0.41/0.58  thf('75', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_D @ 
% 0.41/0.58        (k1_zfmisc_1 @ 
% 0.41/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(cc2_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.58  thf('76', plain,
% 0.41/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.58         ((v4_relat_1 @ X14 @ X15)
% 0.41/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.58  thf('77', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.41/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.41/0.58  thf(d18_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ B ) =>
% 0.41/0.58       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.58  thf('78', plain,
% 0.41/0.58      (![X8 : $i, X9 : $i]:
% 0.41/0.58         (~ (v4_relat_1 @ X8 @ X9)
% 0.41/0.58          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.41/0.58          | ~ (v1_relat_1 @ X8))),
% 0.41/0.58      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.41/0.58  thf('79', plain,
% 0.41/0.58      ((~ (v1_relat_1 @ sk_D)
% 0.41/0.58        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['77', '78'])).
% 0.41/0.58  thf('80', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_D @ 
% 0.41/0.58        (k1_zfmisc_1 @ 
% 0.41/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(cc2_relat_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.58  thf('81', plain,
% 0.41/0.58      (![X6 : $i, X7 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.41/0.58          | (v1_relat_1 @ X6)
% 0.41/0.58          | ~ (v1_relat_1 @ X7))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.58  thf('82', plain,
% 0.41/0.58      ((~ (v1_relat_1 @ 
% 0.41/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.41/0.58        | (v1_relat_1 @ sk_D))),
% 0.41/0.58      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.58  thf(fc6_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.58  thf('83', plain,
% 0.41/0.58      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.41/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.58  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.58      inference('demod', [status(thm)], ['82', '83'])).
% 0.41/0.58  thf('85', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.41/0.58      inference('demod', [status(thm)], ['79', '84'])).
% 0.41/0.58  thf(t97_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ B ) =>
% 0.41/0.58       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.41/0.58         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.41/0.58  thf('86', plain,
% 0.41/0.58      (![X12 : $i, X13 : $i]:
% 0.41/0.58         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.41/0.58          | ((k7_relat_1 @ X12 @ X13) = (X12))
% 0.41/0.58          | ~ (v1_relat_1 @ X12))),
% 0.41/0.58      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.41/0.58  thf('87', plain,
% 0.41/0.58      ((~ (v1_relat_1 @ sk_D)
% 0.41/0.58        | ((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)) = (sk_D)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['85', '86'])).
% 0.41/0.58  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.58      inference('demod', [status(thm)], ['82', '83'])).
% 0.41/0.58  thf('89', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)) = (sk_D))),
% 0.41/0.58      inference('demod', [status(thm)], ['87', '88'])).
% 0.41/0.58  thf('90', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.41/0.58      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.58  thf('91', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.41/0.58      inference('demod', [status(thm)], ['89', '90'])).
% 0.41/0.58  thf('92', plain,
% 0.41/0.58      (((v2_struct_0 @ sk_B)
% 0.41/0.58        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))
% 0.41/0.58        | (v2_struct_0 @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['74', '91'])).
% 0.41/0.58  thf('93', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('94', plain,
% 0.41/0.58      (((v2_struct_0 @ sk_A)
% 0.41/0.58        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.41/0.58      inference('clc', [status(thm)], ['92', '93'])).
% 0.41/0.58  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('96', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.41/0.58      inference('clc', [status(thm)], ['94', '95'])).
% 0.41/0.58  thf('97', plain,
% 0.41/0.58      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.58          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.41/0.58      inference('demod', [status(thm)], ['50', '96'])).
% 0.41/0.58  thf('98', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['47', '97'])).
% 0.41/0.58  thf(fc2_struct_0, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.58  thf('99', plain,
% 0.41/0.58      (![X24 : $i]:
% 0.41/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.41/0.58          | ~ (l1_struct_0 @ X24)
% 0.41/0.58          | (v2_struct_0 @ X24))),
% 0.41/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.58  thf('100', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['98', '99'])).
% 0.41/0.58  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(dt_l1_pre_topc, axiom,
% 0.41/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.58  thf('102', plain,
% 0.41/0.58      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.41/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.58  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.58      inference('sup-', [status(thm)], ['101', '102'])).
% 0.41/0.58  thf('104', plain, ((v2_struct_0 @ sk_A)),
% 0.41/0.58      inference('demod', [status(thm)], ['100', '103'])).
% 0.41/0.58  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
