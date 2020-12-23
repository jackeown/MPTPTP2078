%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqUq5NAOJy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 361 expanded)
%              Number of leaves         :   34 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          : 1263 (9100 expanded)
%              Number of equality atoms :   41 ( 322 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
      | ( X20 = X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

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

thf('12',plain,(
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

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r1_funct_2 @ X23 @ X24 @ X27 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X25 )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('18',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('20',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('26',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('29',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

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

thf('30',plain,(
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

thf('31',plain,(
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
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('36',plain,(
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
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf(t40_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ A @ C )
       => ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X11 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X14 ) ) )
      | ( r2_relset_1 @ X11 @ X14 @ ( k2_partfun1 @ X11 @ X14 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t40_funct_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ sk_D )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) ) @ sk_D ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('58',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X8 @ X9 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['8'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( X3 = X6 )
      | ~ ( r2_relset_1 @ X4 @ X5 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 ) @ X1 )
      | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('69',plain,
    ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ sk_C ) )
    = sk_D ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference('sup+',[status(thm)],['47','69'])).

thf('71',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['26','70'])).

thf('72',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','71'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('73',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('76',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqUq5NAOJy
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:14:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 116 iterations in 0.081s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.55  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.22/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.22/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(t60_tmap_1, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.55             ( l1_pre_topc @ B ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.55                     ( v1_funct_2 @
% 0.22/0.55                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.55                     ( m1_subset_1 @
% 0.22/0.55                       D @ 
% 0.22/0.55                       ( k1_zfmisc_1 @
% 0.22/0.55                         ( k2_zfmisc_1 @
% 0.22/0.55                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.55                   ( ( ( g1_pre_topc @
% 0.22/0.55                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.55                       ( g1_pre_topc @
% 0.22/0.55                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.55                     ( r1_funct_2 @
% 0.22/0.55                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.22/0.55                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.55            ( l1_pre_topc @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.55                ( l1_pre_topc @ B ) ) =>
% 0.22/0.55              ( ![C:$i]:
% 0.22/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.55                  ( ![D:$i]:
% 0.22/0.55                    ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.55                        ( v1_funct_2 @
% 0.22/0.55                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.55                        ( m1_subset_1 @
% 0.22/0.55                          D @ 
% 0.22/0.55                          ( k1_zfmisc_1 @
% 0.22/0.55                            ( k2_zfmisc_1 @
% 0.22/0.55                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.55                      ( ( ( g1_pre_topc @
% 0.22/0.55                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.55                          ( g1_pre_topc @
% 0.22/0.55                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.55                        ( r1_funct_2 @
% 0.22/0.55                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.55                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.22/0.55                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.22/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_u1_pre_topc, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( m1_subset_1 @
% 0.22/0.55         ( u1_pre_topc @ A ) @ 
% 0.22/0.55         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X16 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (u1_pre_topc @ X16) @ 
% 0.22/0.55           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.22/0.55          | ~ (l1_pre_topc @ X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.22/0.55  thf(free_g1_pre_topc, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.55       ( ![C:$i,D:$i]:
% 0.22/0.55         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.22/0.55           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.55         (((g1_pre_topc @ X20 @ X21) != (g1_pre_topc @ X18 @ X19))
% 0.22/0.55          | ((X20) = (X18))
% 0.22/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.22/0.55      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (l1_pre_topc @ X0)
% 0.22/0.55          | ((u1_struct_0 @ X0) = (X1))
% 0.22/0.55          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.22/0.55              != (g1_pre_topc @ X1 @ X2)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.22/0.55          | ((u1_struct_0 @ sk_B) = (X1))
% 0.22/0.55          | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.55  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.55            != (g1_pre_topc @ X1 @ X0))
% 0.22/0.55          | ((u1_struct_0 @ sk_B) = (X1)))),
% 0.22/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.55  thf('9', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.55  thf('10', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['1', '9'])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['1', '9'])).
% 0.22/0.55  thf(redefinition_r1_funct_2, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.55     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.22/0.55         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.22/0.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.55         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.22/0.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.22/0.55       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.22/0.55  thf('12', plain,
% 0.22/0.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.22/0.55          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.22/0.55          | ~ (v1_funct_1 @ X22)
% 0.22/0.55          | (v1_xboole_0 @ X25)
% 0.22/0.55          | (v1_xboole_0 @ X24)
% 0.22/0.55          | ~ (v1_funct_1 @ X26)
% 0.22/0.55          | ~ (v1_funct_2 @ X26 @ X27 @ X25)
% 0.22/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.22/0.55          | (r1_funct_2 @ X23 @ X24 @ X27 @ X25 @ X22 @ X26)
% 0.22/0.55          | ((X22) != (X26)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.55         ((r1_funct_2 @ X23 @ X24 @ X27 @ X25 @ X26 @ X26)
% 0.22/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.22/0.55          | ~ (v1_funct_2 @ X26 @ X27 @ X25)
% 0.22/0.55          | (v1_xboole_0 @ X24)
% 0.22/0.55          | (v1_xboole_0 @ X25)
% 0.22/0.55          | ~ (v1_funct_1 @ X26)
% 0.22/0.55          | ~ (v1_funct_2 @ X26 @ X23 @ X24)
% 0.22/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.22/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | (v1_xboole_0 @ X0)
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.55             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['11', '13'])).
% 0.22/0.55  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('17', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.22/0.55          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | (v1_xboole_0 @ X0)
% 0.22/0.55          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.55             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['14', '15', '18'])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '19'])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.55        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.22/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('25', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['1', '9'])).
% 0.22/0.55  thf('29', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.55  thf(d4_tmap_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.55             ( l1_pre_topc @ B ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.55                 ( m1_subset_1 @
% 0.22/0.55                   C @ 
% 0.22/0.55                   ( k1_zfmisc_1 @
% 0.22/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.55                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.22/0.55                     ( k2_partfun1 @
% 0.22/0.55                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.55                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X28)
% 0.22/0.55          | ~ (v2_pre_topc @ X28)
% 0.22/0.55          | ~ (l1_pre_topc @ X28)
% 0.22/0.55          | ~ (m1_pre_topc @ X29 @ X30)
% 0.22/0.55          | ((k2_tmap_1 @ X30 @ X28 @ X31 @ X29)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28) @ 
% 0.22/0.55                 X31 @ (u1_struct_0 @ X29)))
% 0.22/0.55          | ~ (m1_subset_1 @ X31 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))))
% 0.22/0.55          | ~ (v1_funct_2 @ X31 @ (u1_struct_0 @ X30) @ (u1_struct_0 @ X28))
% 0.22/0.55          | ~ (v1_funct_1 @ X31)
% 0.22/0.55          | ~ (l1_pre_topc @ X30)
% 0.22/0.55          | ~ (v2_pre_topc @ X30)
% 0.22/0.55          | (v2_struct_0 @ X30))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.22/0.55             (k1_zfmisc_1 @ 
% 0.22/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.22/0.55          | (v2_struct_0 @ sk_B)
% 0.22/0.55          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.55          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.55          | ~ (v1_funct_1 @ X1)
% 0.22/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.22/0.55          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.22/0.55                 X1 @ (u1_struct_0 @ X2)))
% 0.22/0.55          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf('32', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('34', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.55  thf('35', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X1 @ 
% 0.22/0.55             (k1_zfmisc_1 @ 
% 0.22/0.55              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.22/0.55          | (v2_struct_0 @ sk_B)
% 0.22/0.55          | ~ (v1_funct_1 @ X1)
% 0.22/0.55          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.22/0.55          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0) @ 
% 0.22/0.55                 X1 @ (u1_struct_0 @ X2)))
% 0.22/0.55          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | ~ (v2_pre_topc @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_A)
% 0.22/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.55          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                 sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.55          | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['28', '36'])).
% 0.22/0.55  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v2_struct_0 @ sk_A)
% 0.22/0.55          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.55          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.55              = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55                 sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.55          | (v2_struct_0 @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['37', '38', '39', '40', '41'])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_B)
% 0.22/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55               sk_D @ (u1_struct_0 @ sk_C)))
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['27', '42'])).
% 0.22/0.55  thf('44', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.55            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55               sk_D @ (u1_struct_0 @ sk_C))))),
% 0.22/0.55      inference('clc', [status(thm)], ['43', '44'])).
% 0.22/0.55  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.55         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55            (u1_struct_0 @ sk_C)))),
% 0.22/0.55      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf(d10_xboole_0, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.55  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.55      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['1', '9'])).
% 0.22/0.55  thf(t40_funct_2, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.55       ( ( r1_tarski @ A @ C ) =>
% 0.22/0.55         ( r2_relset_1 @ A @ B @ ( k2_partfun1 @ A @ B @ D @ C ) @ D ) ) ))).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.55         (~ (r1_tarski @ X11 @ X12)
% 0.22/0.55          | ~ (v1_funct_1 @ X13)
% 0.22/0.55          | ~ (v1_funct_2 @ X13 @ X11 @ X14)
% 0.22/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X14)))
% 0.22/0.55          | (r2_relset_1 @ X11 @ X14 @ (k2_partfun1 @ X11 @ X14 @ X13 @ X12) @ 
% 0.22/0.55             X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [t40_funct_2])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55            X0) @ 
% 0.22/0.55           sk_D)
% 0.22/0.55          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.55          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.55  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55            X0) @ 
% 0.22/0.55           sk_D)
% 0.22/0.55          | ~ (r1_tarski @ (u1_struct_0 @ sk_C) @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      ((r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55        (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55         (u1_struct_0 @ sk_C)) @ 
% 0.22/0.55        sk_D)),
% 0.22/0.55      inference('sup-', [status(thm)], ['49', '55'])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_k2_partfun1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.55       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.22/0.55         ( m1_subset_1 @
% 0.22/0.55           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.22/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.22/0.55          | ~ (v1_funct_1 @ X7)
% 0.22/0.55          | (m1_subset_1 @ (k2_partfun1 @ X8 @ X9 @ X7 @ X10) @ 
% 0.22/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((m1_subset_1 @ 
% 0.22/0.55           (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55            X0) @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.22/0.55          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.55  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('61', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (m1_subset_1 @ 
% 0.22/0.55          (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55           X0) @ 
% 0.22/0.55          (k1_zfmisc_1 @ 
% 0.22/0.55           (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.55  thf('62', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.55  thf('63', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['8'])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (m1_subset_1 @ 
% 0.22/0.55          (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55           X0) @ 
% 0.22/0.55          (k1_zfmisc_1 @ 
% 0.22/0.55           (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.22/0.55  thf(redefinition_r2_relset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.22/0.55  thf('65', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.22/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.22/0.55          | ((X3) = (X6))
% 0.22/0.55          | ~ (r2_relset_1 @ X4 @ X5 @ X3 @ X6))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r2_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55             (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55              sk_D @ X0) @ 
% 0.22/0.55             X1)
% 0.22/0.55          | ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55              sk_D @ X0) = (X1))
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ 
% 0.22/0.55               (k1_zfmisc_1 @ 
% 0.22/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      ((~ (m1_subset_1 @ sk_D @ 
% 0.22/0.55           (k1_zfmisc_1 @ 
% 0.22/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.22/0.55        | ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55            (u1_struct_0 @ sk_C)) = (sk_D)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['56', '66'])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ 
% 0.22/0.55        (k1_zfmisc_1 @ 
% 0.22/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['1', '9'])).
% 0.22/0.55  thf('69', plain,
% 0.22/0.55      (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.55         (u1_struct_0 @ sk_C)) = (sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['67', '68'])).
% 0.22/0.55  thf('70', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.22/0.55      inference('sup+', [status(thm)], ['47', '69'])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.55          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.22/0.55      inference('demod', [status(thm)], ['26', '70'])).
% 0.22/0.55  thf('72', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['23', '71'])).
% 0.22/0.55  thf(fc2_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      (![X17 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.22/0.55          | ~ (l1_struct_0 @ X17)
% 0.22/0.55          | (v2_struct_0 @ X17))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.55  thf('74', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.55  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_l1_pre_topc, axiom,
% 0.22/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.55  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.55  thf('78', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['74', '77'])).
% 0.22/0.55  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
