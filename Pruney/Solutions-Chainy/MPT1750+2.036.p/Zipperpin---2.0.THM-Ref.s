%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9oi8EPDSle

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 688 expanded)
%              Number of leaves         :   40 ( 206 expanded)
%              Depth                    :   23
%              Number of atoms          : 1233 (16298 expanded)
%              Number of equality atoms :   54 ( 668 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( g1_pre_topc @ X20 @ X21 )
       != ( g1_pre_topc @ X18 @ X19 ) )
      | ( X21 = X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( g1_pre_topc @ X20 @ X21 )
       != ( g1_pre_topc @ X18 @ X19 ) )
      | ( X20 = X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ( r1_funct_2 @ X23 @ X24 @ X27 @ X25 @ X22 @ X26 )
      | ( X22 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r1_funct_2 @ X23 @ X24 @ X27 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X25 )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( ( k2_tmap_1 @ X30 @ X28 @ X31 @ X29 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) @ X31 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k2_partfun1 @ X12 @ X13 @ X11 @ X14 )
        = ( k7_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50','57','58','59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('63',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('70',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('71',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','71'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('73',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ( ( k7_relat_1 @ X6 @ X7 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['69','70'])).

thf('76',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    = sk_D ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('78',plain,
    ( ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['37','83'])).

thf('85',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','84'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('86',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('89',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9oi8EPDSle
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:29:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 83 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.49  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.21/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(t60_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.49                     ( v1_funct_2 @
% 0.21/0.49                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49                     ( m1_subset_1 @
% 0.21/0.49                       D @ 
% 0.21/0.49                       ( k1_zfmisc_1 @
% 0.21/0.49                         ( k2_zfmisc_1 @
% 0.21/0.49                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.49                   ( ( ( g1_pre_topc @
% 0.21/0.49                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.21/0.49                       ( g1_pre_topc @
% 0.21/0.49                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.49                     ( r1_funct_2 @
% 0.21/0.49                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.49                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.21/0.49                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50                ( l1_pre_topc @ B ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.50                  ( ![D:$i]:
% 0.21/0.50                    ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.50                        ( v1_funct_2 @
% 0.21/0.50                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50                        ( m1_subset_1 @
% 0.21/0.50                          D @ 
% 0.21/0.50                          ( k1_zfmisc_1 @
% 0.21/0.50                            ( k2_zfmisc_1 @
% 0.21/0.50                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.50                      ( ( ( g1_pre_topc @
% 0.21/0.50                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.21/0.50                          ( g1_pre_topc @
% 0.21/0.50                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.50                        ( r1_funct_2 @
% 0.21/0.50                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.50                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.21/0.50                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_u1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( u1_pre_topc @ A ) @ 
% 0.21/0.50         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X16 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_pre_topc @ X16) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.21/0.50          | ~ (l1_pre_topc @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.50  thf(free_g1_pre_topc, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i,D:$i]:
% 0.21/0.50         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.50           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.50         (((g1_pre_topc @ X20 @ X21) != (g1_pre_topc @ X18 @ X19))
% 0.21/0.50          | ((X21) = (X19))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.21/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X0)
% 0.21/0.50          | ((u1_pre_topc @ X0) = (X1))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.50              != (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.50            != (g1_pre_topc @ X1 @ X0))
% 0.21/0.50          | ((u1_pre_topc @ sk_B) = (X0))
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.50  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.50            != (g1_pre_topc @ X1 @ X0))
% 0.21/0.50          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X16 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_pre_topc @ X16) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.21/0.50          | ~ (l1_pre_topc @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.21/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.50         (((g1_pre_topc @ X20 @ X21) != (g1_pre_topc @ X18 @ X19))
% 0.21/0.50          | ((X20) = (X18))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.21/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((u1_struct_0 @ sk_B) = (X0))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C))
% 0.21/0.50              != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['8'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((u1_struct_0 @ sk_B) = (X0))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.21/0.50              != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.50  thf('20', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['1', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['1', '20'])).
% 0.21/0.50  thf(redefinition_r1_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.50     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.21/0.50         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.50         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.21/0.50         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.21/0.50       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.50          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.50          | ~ (v1_funct_1 @ X22)
% 0.21/0.50          | (v1_xboole_0 @ X25)
% 0.21/0.50          | (v1_xboole_0 @ X24)
% 0.21/0.50          | ~ (v1_funct_1 @ X26)
% 0.21/0.50          | ~ (v1_funct_2 @ X26 @ X27 @ X25)
% 0.21/0.50          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.21/0.50          | (r1_funct_2 @ X23 @ X24 @ X27 @ X25 @ X22 @ X26)
% 0.21/0.50          | ((X22) != (X26)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.50         ((r1_funct_2 @ X23 @ X24 @ X27 @ X25 @ X26 @ X26)
% 0.21/0.50          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.21/0.50          | ~ (v1_funct_2 @ X26 @ X27 @ X25)
% 0.21/0.50          | (v1_xboole_0 @ X24)
% 0.21/0.50          | (v1_xboole_0 @ X25)
% 0.21/0.50          | ~ (v1_funct_1 @ X26)
% 0.21/0.50          | ~ (v1_funct_2 @ X26 @ X23 @ X24)
% 0.21/0.50          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v1_xboole_0 @ X0)
% 0.21/0.50          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '24'])).
% 0.21/0.50  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['19'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v1_xboole_0 @ X0)
% 0.21/0.50          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.50             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.21/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.50          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('36', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['19'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.50          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['1', '20'])).
% 0.21/0.50  thf('40', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['19'])).
% 0.21/0.50  thf(d4_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.50             ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                 ( m1_subset_1 @
% 0.21/0.50                   C @ 
% 0.21/0.50                   ( k1_zfmisc_1 @
% 0.21/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.50                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.21/0.50                     ( k2_partfun1 @
% 0.21/0.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.50                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X28)
% 0.21/0.50          | ~ (v2_pre_topc @ X28)
% 0.21/0.50          | ~ (l1_pre_topc @ X28)
% 0.21/0.50          | ~ (m1_pre_topc @ X29 @ X30)
% 0.21/0.50          | ((k2_tmap_1 @ X30 @ X28 @ X31 @ X29)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28) @ 
% 0.21/0.50                 X31 @ (u1_struct_0 @ X29)))
% 0.21/0.50          | ~ (m1_subset_1 @ X31 @ 
% 0.21/0.50               (k1_zfmisc_1 @ 
% 0.21/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))))
% 0.21/0.50          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))
% 0.21/0.50          | ~ (v1_funct_1 @ X31)
% 0.21/0.50          | ~ (l1_pre_topc @ X30)
% 0.21/0.50          | ~ (v2_pre_topc @ X30)
% 0.21/0.50          | (v2_struct_0 @ X30))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ 
% 0.21/0.50             (k1_zfmisc_1 @ 
% 0.21/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.50          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.21/0.50                 X1 @ (u1_struct_0 @ X2)))
% 0.21/0.50          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['19'])).
% 0.21/0.50  thf('46', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['19'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X1 @ 
% 0.21/0.50             (k1_zfmisc_1 @ 
% 0.21/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.21/0.50          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.21/0.50                 X1 @ (u1_struct_0 @ X2)))
% 0.21/0.50          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (v2_pre_topc @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.50          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.21/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50                 sk_D @ (u1_struct_0 @ X0)))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '47'])).
% 0.21/0.50  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k2_partfun1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.50          | ~ (v1_funct_1 @ X11)
% 0.21/0.50          | ((k2_partfun1 @ X12 @ X13 @ X11 @ X14) = (k7_relat_1 @ X11 @ X14)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.50            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.50           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['19'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.21/0.50           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.50          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.21/0.50              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.21/0.50          | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['48', '49', '50', '57', '58', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.21/0.50            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         ((v4_relat_1 @ X8 @ X9)
% 0.21/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('64', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf(d18_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (v4_relat_1 @ X2 @ X3)
% 0.21/0.50          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.21/0.50          | ~ (v1_relat_1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.50        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.21/0.50          | (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ 
% 0.21/0.50           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | (v1_relat_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.50  thf(fc6_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.50  thf('71', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('72', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['66', '71'])).
% 0.21/0.50  thf(t97_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.21/0.50         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.21/0.50          | ((k7_relat_1 @ X6 @ X7) = (X6))
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.50        | ((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)) = (sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('76', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)) = (sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.50  thf('77', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['19'])).
% 0.21/0.50  thf('78', plain, (((k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.21/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['61', '78'])).
% 0.21/0.50  thf('80', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.21/0.50      inference('clc', [status(thm)], ['79', '80'])).
% 0.21/0.50  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('83', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.21/0.50      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '83'])).
% 0.21/0.50  thf('85', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '84'])).
% 0.21/0.50  thf(fc2_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (![X17 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.21/0.50          | ~ (l1_struct_0 @ X17)
% 0.21/0.50          | (v2_struct_0 @ X17))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.50  thf('87', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.50  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.50  thf('91', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['87', '90'])).
% 0.21/0.50  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
