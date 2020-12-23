%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pD16i6Xwka

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:43 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 682 expanded)
%              Number of leaves         :   39 ( 204 expanded)
%              Depth                    :   23
%              Number of atoms          : 1201 (16263 expanded)
%              Number of equality atoms :   52 ( 667 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( g1_pre_topc @ X21 @ X22 )
       != ( g1_pre_topc @ X19 @ X20 ) )
      | ( X22 = X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
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
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( g1_pre_topc @ X21 @ X22 )
       != ( g1_pre_topc @ X19 @ X20 ) )
      | ( X21 = X19 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
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

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( r1_funct_2 @ X24 @ X25 @ X28 @ X26 @ X23 @ X27 )
      | ( X23 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r1_funct_2 @ X24 @ X25 @ X28 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf('31',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('33',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('37',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','20'])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

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

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ( ( k2_tmap_1 @ X31 @ X29 @ X32 @ X30 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) @ X32 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('42',plain,(
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
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('46',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('47',plain,(
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
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','20'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('52',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( ( k2_partfun1 @ X11 @ X12 @ X10 @ X13 )
        = ( k7_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50','55','56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('66',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','67'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( ( k7_relat_1 @ X2 @ X3 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['65','66'])).

thf('72',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    = sk_D ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('74',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['37','79'])).

thf('81',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','80'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('85',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pD16i6Xwka
% 0.13/0.37  % Computer   : n012.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:43:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 81 iterations in 0.043s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.23/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.53  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.53  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.23/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.53  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.23/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.53  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.23/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.53  thf(t60_tmap_1, conjecture,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.23/0.53             ( l1_pre_topc @ B ) ) =>
% 0.23/0.53           ( ![C:$i]:
% 0.23/0.53             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.23/0.53               ( ![D:$i]:
% 0.23/0.53                 ( ( ( v1_funct_1 @ D ) & 
% 0.23/0.53                     ( v1_funct_2 @
% 0.23/0.53                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.23/0.53                     ( m1_subset_1 @
% 0.23/0.53                       D @ 
% 0.23/0.53                       ( k1_zfmisc_1 @
% 0.23/0.53                         ( k2_zfmisc_1 @
% 0.23/0.53                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.23/0.53                   ( ( ( g1_pre_topc @
% 0.23/0.53                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.23/0.53                       ( g1_pre_topc @
% 0.23/0.53                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.23/0.53                     ( r1_funct_2 @
% 0.23/0.53                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.23/0.53                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.23/0.53                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i]:
% 0.23/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.53            ( l1_pre_topc @ A ) ) =>
% 0.23/0.53          ( ![B:$i]:
% 0.23/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.23/0.53                ( l1_pre_topc @ B ) ) =>
% 0.23/0.53              ( ![C:$i]:
% 0.23/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.23/0.53                  ( ![D:$i]:
% 0.23/0.53                    ( ( ( v1_funct_1 @ D ) & 
% 0.23/0.53                        ( v1_funct_2 @
% 0.23/0.53                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.23/0.53                        ( m1_subset_1 @
% 0.23/0.53                          D @ 
% 0.23/0.53                          ( k1_zfmisc_1 @
% 0.23/0.53                            ( k2_zfmisc_1 @
% 0.23/0.53                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.23/0.53                      ( ( ( g1_pre_topc @
% 0.23/0.53                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.23/0.53                          ( g1_pre_topc @
% 0.23/0.53                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.23/0.53                        ( r1_funct_2 @
% 0.23/0.53                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.23/0.53                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.23/0.53                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.23/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('1', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(dt_u1_pre_topc, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_pre_topc @ A ) =>
% 0.23/0.53       ( m1_subset_1 @
% 0.23/0.53         ( u1_pre_topc @ A ) @ 
% 0.23/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      (![X17 : $i]:
% 0.23/0.53         ((m1_subset_1 @ (u1_pre_topc @ X17) @ 
% 0.23/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.23/0.53          | ~ (l1_pre_topc @ X17))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.23/0.53  thf(free_g1_pre_topc, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.53       ( ![C:$i,D:$i]:
% 0.23/0.53         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.23/0.53           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.53         (((g1_pre_topc @ X21 @ X22) != (g1_pre_topc @ X19 @ X20))
% 0.23/0.53          | ((X22) = (X20))
% 0.23/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.23/0.53      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.23/0.53  thf('5', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (l1_pre_topc @ X0)
% 0.23/0.53          | ((u1_pre_topc @ X0) = (X1))
% 0.23/0.53          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.23/0.53              != (g1_pre_topc @ X2 @ X1)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53            != (g1_pre_topc @ X1 @ X0))
% 0.23/0.53          | ((u1_pre_topc @ sk_B) = (X0))
% 0.23/0.53          | ~ (l1_pre_topc @ sk_B))),
% 0.23/0.53      inference('sup-', [status(thm)], ['2', '5'])).
% 0.23/0.53  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53            != (g1_pre_topc @ X1 @ X0))
% 0.23/0.53          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.23/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.23/0.53  thf('9', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['8'])).
% 0.23/0.53  thf('10', plain,
% 0.23/0.53      (![X17 : $i]:
% 0.23/0.53         ((m1_subset_1 @ (u1_pre_topc @ X17) @ 
% 0.23/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))
% 0.23/0.53          | ~ (l1_pre_topc @ X17))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.23/0.53  thf('11', plain,
% 0.23/0.53      (((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.23/0.53         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.23/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.23/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.23/0.53  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('13', plain,
% 0.23/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.23/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.23/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.23/0.53  thf('14', plain,
% 0.23/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.53         (((g1_pre_topc @ X21 @ X22) != (g1_pre_topc @ X19 @ X20))
% 0.23/0.53          | ((X21) = (X19))
% 0.23/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.23/0.53      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.23/0.53  thf('15', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((u1_struct_0 @ sk_B) = (X0))
% 0.23/0.53          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C))
% 0.23/0.53              != (g1_pre_topc @ X0 @ X1)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.53  thf('16', plain,
% 0.23/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('17', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['8'])).
% 0.23/0.53  thf('18', plain,
% 0.23/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.23/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.53  thf('19', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (((u1_struct_0 @ sk_B) = (X0))
% 0.23/0.53          | ((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.23/0.53              != (g1_pre_topc @ X0 @ X1)))),
% 0.23/0.53      inference('demod', [status(thm)], ['15', '18'])).
% 0.23/0.53  thf('20', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['19'])).
% 0.23/0.53  thf('21', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['1', '20'])).
% 0.23/0.53  thf('22', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['1', '20'])).
% 0.23/0.53  thf(redefinition_r1_funct_2, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.23/0.53     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.23/0.53         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.23/0.53         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.23/0.53         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.23/0.53         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.23/0.53       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.23/0.53  thf('23', plain,
% 0.23/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.23/0.53          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.23/0.53          | ~ (v1_funct_1 @ X23)
% 0.23/0.53          | (v1_xboole_0 @ X26)
% 0.23/0.53          | (v1_xboole_0 @ X25)
% 0.23/0.53          | ~ (v1_funct_1 @ X27)
% 0.23/0.53          | ~ (v1_funct_2 @ X27 @ X28 @ X26)
% 0.23/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.23/0.53          | (r1_funct_2 @ X24 @ X25 @ X28 @ X26 @ X23 @ X27)
% 0.23/0.53          | ((X23) != (X27)))),
% 0.23/0.53      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.23/0.53  thf('24', plain,
% 0.23/0.53      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.23/0.53         ((r1_funct_2 @ X24 @ X25 @ X28 @ X26 @ X27 @ X27)
% 0.23/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.23/0.53          | ~ (v1_funct_2 @ X27 @ X28 @ X26)
% 0.23/0.53          | (v1_xboole_0 @ X25)
% 0.23/0.53          | (v1_xboole_0 @ X26)
% 0.23/0.53          | ~ (v1_funct_1 @ X27)
% 0.23/0.53          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 0.23/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.23/0.53      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.53  thf('25', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.23/0.53          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.23/0.53          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | (v1_xboole_0 @ X0)
% 0.23/0.53          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.23/0.53             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.23/0.53      inference('sup-', [status(thm)], ['22', '24'])).
% 0.23/0.53  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('27', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('28', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['19'])).
% 0.23/0.53  thf('29', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.53  thf('30', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.23/0.53          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.23/0.53          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | (v1_xboole_0 @ X0)
% 0.23/0.53          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.23/0.53             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.23/0.53      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.23/0.53  thf('31', plain,
% 0.23/0.53      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['21', '30'])).
% 0.23/0.53  thf('32', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.53  thf('33', plain,
% 0.23/0.53      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.23/0.53  thf('34', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.23/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.23/0.53  thf('35', plain,
% 0.23/0.53      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('36', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['19'])).
% 0.23/0.53  thf('37', plain,
% 0.23/0.53      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.23/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.53  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('39', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['1', '20'])).
% 0.23/0.53  thf('40', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['19'])).
% 0.23/0.53  thf(d4_tmap_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.23/0.53             ( l1_pre_topc @ B ) ) =>
% 0.23/0.53           ( ![C:$i]:
% 0.23/0.53             ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.53                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.23/0.53                 ( m1_subset_1 @
% 0.23/0.53                   C @ 
% 0.23/0.53                   ( k1_zfmisc_1 @
% 0.23/0.53                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.23/0.53               ( ![D:$i]:
% 0.23/0.53                 ( ( m1_pre_topc @ D @ A ) =>
% 0.23/0.53                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.23/0.53                     ( k2_partfun1 @
% 0.23/0.53                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.23/0.53                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.53  thf('41', plain,
% 0.23/0.53      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.23/0.53         ((v2_struct_0 @ X29)
% 0.23/0.53          | ~ (v2_pre_topc @ X29)
% 0.23/0.53          | ~ (l1_pre_topc @ X29)
% 0.23/0.53          | ~ (m1_pre_topc @ X30 @ X31)
% 0.23/0.53          | ((k2_tmap_1 @ X31 @ X29 @ X32 @ X30)
% 0.23/0.53              = (k2_partfun1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29) @ 
% 0.23/0.53                 X32 @ (u1_struct_0 @ X30)))
% 0.23/0.53          | ~ (m1_subset_1 @ X32 @ 
% 0.23/0.53               (k1_zfmisc_1 @ 
% 0.23/0.53                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))))
% 0.23/0.53          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))
% 0.23/0.53          | ~ (v1_funct_1 @ X32)
% 0.23/0.53          | ~ (l1_pre_topc @ X31)
% 0.23/0.53          | ~ (v2_pre_topc @ X31)
% 0.23/0.53          | (v2_struct_0 @ X31))),
% 0.23/0.53      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.23/0.53  thf('42', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X1 @ 
% 0.23/0.53             (k1_zfmisc_1 @ 
% 0.23/0.53              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.23/0.53          | (v2_struct_0 @ sk_B)
% 0.23/0.53          | ~ (v2_pre_topc @ sk_B)
% 0.23/0.53          | ~ (l1_pre_topc @ sk_B)
% 0.23/0.53          | ~ (v1_funct_1 @ X1)
% 0.23/0.53          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.23/0.53          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.23/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.23/0.53                 X1 @ (u1_struct_0 @ X2)))
% 0.23/0.53          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.23/0.53          | ~ (l1_pre_topc @ X0)
% 0.23/0.53          | ~ (v2_pre_topc @ X0)
% 0.23/0.53          | (v2_struct_0 @ X0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.23/0.53  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('45', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['19'])).
% 0.23/0.53  thf('46', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['19'])).
% 0.23/0.53  thf('47', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X1 @ 
% 0.23/0.53             (k1_zfmisc_1 @ 
% 0.23/0.53              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.23/0.53          | (v2_struct_0 @ sk_B)
% 0.23/0.53          | ~ (v1_funct_1 @ X1)
% 0.23/0.53          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.23/0.53          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.23/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.23/0.53                 X1 @ (u1_struct_0 @ X2)))
% 0.23/0.53          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.23/0.53          | ~ (l1_pre_topc @ X0)
% 0.23/0.53          | ~ (v2_pre_topc @ X0)
% 0.23/0.53          | (v2_struct_0 @ X0))),
% 0.23/0.53      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.23/0.53  thf('48', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((v2_struct_0 @ sk_A)
% 0.23/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.23/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.23/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.23/0.53          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.23/0.53              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53                 sk_D @ (u1_struct_0 @ X0)))
% 0.23/0.53          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.23/0.53          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.53          | (v2_struct_0 @ sk_B))),
% 0.23/0.53      inference('sup-', [status(thm)], ['39', '47'])).
% 0.23/0.53  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('51', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('demod', [status(thm)], ['1', '20'])).
% 0.23/0.53  thf(redefinition_k2_partfun1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.53     ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.53       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.23/0.53  thf('52', plain,
% 0.23/0.53      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.23/0.53          | ~ (v1_funct_1 @ X10)
% 0.23/0.53          | ((k2_partfun1 @ X11 @ X12 @ X10 @ X13) = (k7_relat_1 @ X10 @ X13)))),
% 0.23/0.53      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.23/0.53  thf('53', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.23/0.53          | ~ (v1_funct_1 @ sk_D))),
% 0.23/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.23/0.53  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('55', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.23/0.53           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.23/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.23/0.53  thf('56', plain,
% 0.23/0.53      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.53  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('58', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((v2_struct_0 @ sk_A)
% 0.23/0.53          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.23/0.53          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.23/0.53              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.23/0.53          | (v2_struct_0 @ sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['48', '49', '50', '55', '56', '57'])).
% 0.23/0.53  thf('59', plain,
% 0.23/0.53      (((v2_struct_0 @ sk_B)
% 0.23/0.53        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.23/0.53            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.23/0.53        | (v2_struct_0 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['38', '58'])).
% 0.23/0.53  thf('60', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc2_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.53  thf('61', plain,
% 0.23/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.53         ((v4_relat_1 @ X7 @ X8)
% 0.23/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.53  thf('62', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.23/0.53  thf(d18_relat_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ B ) =>
% 0.23/0.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.53  thf('63', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (v4_relat_1 @ X0 @ X1)
% 0.23/0.53          | (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.23/0.53          | ~ (v1_relat_1 @ X0))),
% 0.23/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.23/0.53  thf('64', plain,
% 0.23/0.53      ((~ (v1_relat_1 @ sk_D)
% 0.23/0.53        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.23/0.53  thf('65', plain,
% 0.23/0.53      ((m1_subset_1 @ sk_D @ 
% 0.23/0.53        (k1_zfmisc_1 @ 
% 0.23/0.53         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(cc1_relset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.53       ( v1_relat_1 @ C ) ))).
% 0.23/0.53  thf('66', plain,
% 0.23/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.53         ((v1_relat_1 @ X4)
% 0.23/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.23/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.53  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.53  thf('68', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['64', '67'])).
% 0.23/0.53  thf(t97_relat_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ B ) =>
% 0.23/0.53       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.23/0.53         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.23/0.53  thf('69', plain,
% 0.23/0.53      (![X2 : $i, X3 : $i]:
% 0.23/0.53         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.23/0.53          | ((k7_relat_1 @ X2 @ X3) = (X2))
% 0.23/0.53          | ~ (v1_relat_1 @ X2))),
% 0.23/0.53      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.23/0.53  thf('70', plain,
% 0.23/0.53      ((~ (v1_relat_1 @ sk_D)
% 0.23/0.53        | ((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)) = (sk_D)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['68', '69'])).
% 0.23/0.53  thf('71', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.23/0.53  thf('72', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)) = (sk_D))),
% 0.23/0.53      inference('demod', [status(thm)], ['70', '71'])).
% 0.23/0.53  thf('73', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.23/0.53      inference('eq_res', [status(thm)], ['19'])).
% 0.23/0.53  thf('74', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.23/0.53      inference('demod', [status(thm)], ['72', '73'])).
% 0.23/0.53  thf('75', plain,
% 0.23/0.53      (((v2_struct_0 @ sk_B)
% 0.23/0.53        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))
% 0.23/0.53        | (v2_struct_0 @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['59', '74'])).
% 0.23/0.53  thf('76', plain, (~ (v2_struct_0 @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('77', plain,
% 0.23/0.53      (((v2_struct_0 @ sk_A)
% 0.23/0.53        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.23/0.53      inference('clc', [status(thm)], ['75', '76'])).
% 0.23/0.53  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('79', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.23/0.53      inference('clc', [status(thm)], ['77', '78'])).
% 0.23/0.53  thf('80', plain,
% 0.23/0.53      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.23/0.53          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.23/0.53      inference('demod', [status(thm)], ['37', '79'])).
% 0.23/0.53  thf('81', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('clc', [status(thm)], ['34', '80'])).
% 0.23/0.53  thf(fc2_struct_0, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.53  thf('82', plain,
% 0.23/0.53      (![X18 : $i]:
% 0.23/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 0.23/0.53          | ~ (l1_struct_0 @ X18)
% 0.23/0.53          | (v2_struct_0 @ X18))),
% 0.23/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.53  thf('83', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.23/0.53  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(dt_l1_pre_topc, axiom,
% 0.23/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.53  thf('85', plain,
% 0.23/0.53      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.23/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.23/0.53  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.53      inference('sup-', [status(thm)], ['84', '85'])).
% 0.23/0.53  thf('87', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('demod', [status(thm)], ['83', '86'])).
% 0.23/0.53  thf('88', plain, ($false), inference('demod', [status(thm)], ['0', '87'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
