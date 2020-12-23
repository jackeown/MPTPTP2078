%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Oev18L9jHO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 301 expanded)
%              Number of leaves         :   37 ( 102 expanded)
%              Depth                    :   24
%              Number of atoms          : 1414 (6189 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t109_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                   => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) )
                     => ( r1_tmap_1 @ C @ ( k6_tmap_1 @ A @ B ) @ ( k2_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t109_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ( v2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t108_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r1_tmap_1 @ A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r2_hidden @ X24 @ X22 )
      | ( r1_tmap_1 @ X23 @ ( k6_tmap_1 @ X23 @ X22 ) @ ( k7_tmap_1 @ X23 @ X22 ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t108_tmap_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_D @ sk_B_1 )
    | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_D )
    | ( r2_hidden @ sk_D @ sk_B_1 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(t64_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( r1_tmap_1 @ X26 @ X28 @ ( k2_tmap_1 @ X25 @ X28 @ X29 @ X26 ) @ X27 )
      | ( X30 != X27 )
      | ~ ( r1_tmap_1 @ X25 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r1_tmap_1 @ X25 @ X28 @ X29 @ X27 )
      | ( r1_tmap_1 @ X26 @ X28 @ ( k2_tmap_1 @ X25 @ X28 @ X29 @ X26 ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X18 @ X19 ) @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('44',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('52',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('60',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('68',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','49','57','65','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B_1 )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B_1 )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( r1_tmap_1 @ sk_C_1 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ sk_B_1 ) @ sk_C_1 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r2_hidden @ sk_D @ sk_B_1 )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc4_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) )
        & ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ) )).

thf('84',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('85',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( r2_hidden @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r2_hidden @ sk_D @ sk_B_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r2_hidden @ sk_D @ sk_B_1 ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','95'])).

thf(rc6_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ~ ( v2_tops_1 @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('97',plain,(
    ! [X15: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc6_tops_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('98',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('108',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['100','105','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_xboole_0 @ ( sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X15 ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[rc6_tops_1])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ~ ( v2_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('118',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['103','104'])).

thf('119',plain,(
    v2_struct_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['0','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Oev18L9jHO
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:35:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 86 iterations in 0.055s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.51  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.51  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.19/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.51  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.19/0.51  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.19/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(t109_tmap_1, conjecture,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.51               ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.19/0.51                 ( ![D:$i]:
% 0.19/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.51                     ( r1_tmap_1 @
% 0.19/0.51                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.19/0.51                       ( k2_tmap_1 @
% 0.19/0.51                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.19/0.51                       D ) ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i]:
% 0.19/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.51            ( l1_pre_topc @ A ) ) =>
% 0.19/0.51          ( ![B:$i]:
% 0.19/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51              ( ![C:$i]:
% 0.19/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.51                  ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.19/0.51                    ( ![D:$i]:
% 0.19/0.51                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.51                        ( r1_tmap_1 @
% 0.19/0.51                          C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.19/0.51                          ( k2_tmap_1 @
% 0.19/0.51                            A @ ( k6_tmap_1 @ A @ B ) @ 
% 0.19/0.51                            ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.19/0.51                          D ) ) ) ) ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t109_tmap_1])).
% 0.19/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain, ((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('2', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t2_subset, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X6 : $i, X7 : $i]:
% 0.19/0.51         ((r2_hidden @ X6 @ X7)
% 0.19/0.51          | (v1_xboole_0 @ X7)
% 0.19/0.51          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.19/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.19/0.51        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf(t3_xboole_0, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X2 @ X0)
% 0.19/0.51          | ~ (r2_hidden @ X2 @ X3)
% 0.19/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))
% 0.19/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ X0)
% 0.19/0.51          | ~ (r2_hidden @ sk_D @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      ((~ (r2_hidden @ sk_D @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_C_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '6'])).
% 0.19/0.51  thf('8', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('9', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('10', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t55_pre_topc, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.51               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X12)
% 0.19/0.51          | ~ (m1_pre_topc @ X12 @ X13)
% 0.19/0.51          | (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.19/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.19/0.51          | ~ (l1_pre_topc @ X13)
% 0.19/0.51          | (v2_struct_0 @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X0)
% 0.19/0.51          | ~ (l1_pre_topc @ X0)
% 0.19/0.51          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.51          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.19/0.51          | (v2_struct_0 @ sk_C_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_C_1)
% 0.19/0.51        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.19/0.51  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_C_1)
% 0.19/0.51        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.51  thf('16', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A) | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.19/0.51  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('19', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t108_tmap_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.51               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.19/0.51                 ( r1_tmap_1 @
% 0.19/0.51                   A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.19/0.51          | (r2_hidden @ X24 @ X22)
% 0.19/0.51          | (r1_tmap_1 @ X23 @ (k6_tmap_1 @ X23 @ X22) @ 
% 0.19/0.51             (k7_tmap_1 @ X23 @ X22) @ X24)
% 0.19/0.51          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.19/0.51          | ~ (l1_pre_topc @ X23)
% 0.19/0.51          | ~ (v2_pre_topc @ X23)
% 0.19/0.51          | (v2_struct_0 @ X23))),
% 0.19/0.51      inference('cnf', [status(esa)], [t108_tmap_1])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51             (k7_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 0.19/0.51          | (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.51  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.19/0.51          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51             (k7_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 0.19/0.51          | (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      (((r2_hidden @ sk_D @ sk_B_1)
% 0.19/0.51        | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51           (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_D)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['19', '25'])).
% 0.19/0.51  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      (((r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51         (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_D)
% 0.19/0.51        | (r2_hidden @ sk_D @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['26', '27'])).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(dt_k7_tmap_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.51         ( l1_pre_topc @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.51       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.19/0.51         ( v1_funct_2 @
% 0.19/0.51           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.51           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.19/0.51         ( m1_subset_1 @
% 0.19/0.51           ( k7_tmap_1 @ A @ B ) @ 
% 0.19/0.51           ( k1_zfmisc_1 @
% 0.19/0.51             ( k2_zfmisc_1 @
% 0.19/0.51               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X18)
% 0.19/0.51          | ~ (v2_pre_topc @ X18)
% 0.19/0.51          | (v2_struct_0 @ X18)
% 0.19/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.51          | (m1_subset_1 @ (k7_tmap_1 @ X18 @ X19) @ 
% 0.19/0.51             (k1_zfmisc_1 @ 
% 0.19/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ 
% 0.19/0.51               (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51         (k1_zfmisc_1 @ 
% 0.19/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.51  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51         (k1_zfmisc_1 @ 
% 0.19/0.51          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))))
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.19/0.51  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51        (k1_zfmisc_1 @ 
% 0.19/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.19/0.51      inference('clc', [status(thm)], ['34', '35'])).
% 0.19/0.51  thf(t64_tmap_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.51             ( l1_pre_topc @ B ) ) =>
% 0.19/0.51           ( ![C:$i]:
% 0.19/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.51                 ( m1_subset_1 @
% 0.19/0.51                   C @ 
% 0.19/0.51                   ( k1_zfmisc_1 @
% 0.19/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.51               ( ![D:$i]:
% 0.19/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.51                   ( ![E:$i]:
% 0.19/0.51                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.51                       ( ![F:$i]:
% 0.19/0.51                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.51                           ( ( ( ( E ) = ( F ) ) & 
% 0.19/0.51                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.19/0.51                             ( r1_tmap_1 @
% 0.19/0.51                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.51  thf('37', plain,
% 0.19/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X25)
% 0.19/0.51          | ~ (v2_pre_topc @ X25)
% 0.19/0.51          | ~ (l1_pre_topc @ X25)
% 0.19/0.51          | (v2_struct_0 @ X26)
% 0.19/0.51          | ~ (m1_pre_topc @ X26 @ X25)
% 0.19/0.51          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.19/0.51          | (r1_tmap_1 @ X26 @ X28 @ (k2_tmap_1 @ X25 @ X28 @ X29 @ X26) @ X27)
% 0.19/0.51          | ((X30) != (X27))
% 0.19/0.51          | ~ (r1_tmap_1 @ X25 @ X28 @ X29 @ X30)
% 0.19/0.51          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X25))
% 0.19/0.51          | ~ (m1_subset_1 @ X29 @ 
% 0.19/0.51               (k1_zfmisc_1 @ 
% 0.19/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28))))
% 0.19/0.51          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28))
% 0.19/0.51          | ~ (v1_funct_1 @ X29)
% 0.19/0.51          | ~ (l1_pre_topc @ X28)
% 0.19/0.51          | ~ (v2_pre_topc @ X28)
% 0.19/0.51          | (v2_struct_0 @ X28))),
% 0.19/0.51      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X28)
% 0.19/0.51          | ~ (v2_pre_topc @ X28)
% 0.19/0.51          | ~ (l1_pre_topc @ X28)
% 0.19/0.51          | ~ (v1_funct_1 @ X29)
% 0.19/0.51          | ~ (v1_funct_2 @ X29 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28))
% 0.19/0.51          | ~ (m1_subset_1 @ X29 @ 
% 0.19/0.51               (k1_zfmisc_1 @ 
% 0.19/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X28))))
% 0.19/0.51          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 0.19/0.51          | ~ (r1_tmap_1 @ X25 @ X28 @ X29 @ X27)
% 0.19/0.51          | (r1_tmap_1 @ X26 @ X28 @ (k2_tmap_1 @ X25 @ X28 @ X29 @ X26) @ X27)
% 0.19/0.51          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.19/0.51          | ~ (m1_pre_topc @ X26 @ X25)
% 0.19/0.51          | (v2_struct_0 @ X26)
% 0.19/0.51          | ~ (l1_pre_topc @ X25)
% 0.19/0.51          | ~ (v2_pre_topc @ X25)
% 0.19/0.51          | (v2_struct_0 @ X25))),
% 0.19/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.51          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51              (k7_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.19/0.51             X1)
% 0.19/0.51          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51               (k7_tmap_1 @ sk_A @ sk_B_1) @ X1)
% 0.19/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.19/0.51          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51               (u1_struct_0 @ sk_A) @ 
% 0.19/0.51               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.19/0.51          | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['36', '38'])).
% 0.19/0.51  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X18)
% 0.19/0.51          | ~ (v2_pre_topc @ X18)
% 0.19/0.51          | (v2_struct_0 @ X18)
% 0.19/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.51          | (v1_funct_2 @ (k7_tmap_1 @ X18 @ X19) @ (u1_struct_0 @ X18) @ 
% 0.19/0.51             (u1_struct_0 @ (k6_tmap_1 @ X18 @ X19))))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.19/0.51  thf('44', plain,
% 0.19/0.51      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.51  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.19/0.51  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.51        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('clc', [status(thm)], ['47', '48'])).
% 0.19/0.51  thf('50', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('51', plain,
% 0.19/0.51      (![X18 : $i, X19 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X18)
% 0.19/0.51          | ~ (v2_pre_topc @ X18)
% 0.19/0.51          | (v2_struct_0 @ X18)
% 0.19/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.51          | (v1_funct_1 @ (k7_tmap_1 @ X18 @ X19)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.19/0.51  thf('52', plain,
% 0.19/0.51      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.19/0.51  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('55', plain,
% 0.19/0.51      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.19/0.51  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('57', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['55', '56'])).
% 0.19/0.51  thf('58', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(dt_k6_tmap_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.51         ( l1_pre_topc @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.51       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.19/0.51         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.19/0.51         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.19/0.51  thf('59', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X16)
% 0.19/0.51          | ~ (v2_pre_topc @ X16)
% 0.19/0.51          | (v2_struct_0 @ X16)
% 0.19/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.51          | (l1_pre_topc @ (k6_tmap_1 @ X16 @ X17)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.19/0.51  thf('60', plain,
% 0.19/0.51      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.51  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('63', plain,
% 0.19/0.51      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.19/0.51  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('65', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['63', '64'])).
% 0.19/0.51  thf('66', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('67', plain,
% 0.19/0.51      (![X16 : $i, X17 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X16)
% 0.19/0.51          | ~ (v2_pre_topc @ X16)
% 0.19/0.51          | (v2_struct_0 @ X16)
% 0.19/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.51          | (v2_pre_topc @ (k6_tmap_1 @ X16 @ X17)))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.19/0.51  thf('68', plain,
% 0.19/0.51      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['66', '67'])).
% 0.19/0.51  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('71', plain,
% 0.19/0.51      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.19/0.51  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('73', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['71', '72'])).
% 0.19/0.51  thf('74', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((v2_struct_0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.51          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51              (k7_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.19/0.51             X1)
% 0.19/0.51          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51               (k7_tmap_1 @ sk_A @ sk_B_1) @ X1)
% 0.19/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.19/0.51          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)))),
% 0.19/0.51      inference('demod', [status(thm)],
% 0.19/0.51                ['39', '40', '41', '49', '57', '65', '73'])).
% 0.19/0.51  thf('75', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ sk_D @ sk_B_1)
% 0.19/0.51          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.19/0.51          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51              (k7_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.19/0.51             sk_D)
% 0.19/0.51          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['28', '74'])).
% 0.19/0.51  thf('76', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.19/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('77', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ sk_D @ sk_B_1)
% 0.19/0.51          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51              (k7_tmap_1 @ sk_A @ sk_B_1) @ X0) @ 
% 0.19/0.51             sk_D)
% 0.19/0.51          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.19/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.51          | (v2_struct_0 @ X0)
% 0.19/0.51          | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['75', '76'])).
% 0.19/0.51  thf('78', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_C_1)
% 0.19/0.51        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.19/0.51        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51            (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_C_1) @ 
% 0.19/0.51           sk_D)
% 0.19/0.51        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51        | (r2_hidden @ sk_D @ sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '77'])).
% 0.19/0.51  thf('79', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('80', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_C_1)
% 0.19/0.51        | (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51            (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_C_1) @ 
% 0.19/0.51           sk_D)
% 0.19/0.51        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51        | (r2_hidden @ sk_D @ sk_B_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['78', '79'])).
% 0.19/0.51  thf('81', plain,
% 0.19/0.51      (~ (r1_tmap_1 @ sk_C_1 @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51          (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.19/0.51           (k7_tmap_1 @ sk_A @ sk_B_1) @ sk_C_1) @ 
% 0.19/0.51          sk_D)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('82', plain,
% 0.19/0.51      (((r2_hidden @ sk_D @ sk_B_1)
% 0.19/0.51        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_C_1)
% 0.19/0.51        | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['80', '81'])).
% 0.19/0.51  thf('83', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(fc4_tmap_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.51         ( l1_pre_topc @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.51       ( ( ~( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.19/0.51         ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.19/0.51         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.19/0.51  thf('84', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i]:
% 0.19/0.51         (~ (l1_pre_topc @ X20)
% 0.19/0.51          | ~ (v2_pre_topc @ X20)
% 0.19/0.51          | (v2_struct_0 @ X20)
% 0.19/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.51          | ~ (v2_struct_0 @ (k6_tmap_1 @ X20 @ X21)))),
% 0.19/0.51      inference('cnf', [status(esa)], [fc4_tmap_1])).
% 0.19/0.51  thf('85', plain,
% 0.19/0.51      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))
% 0.19/0.51        | (v2_struct_0 @ sk_A)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.19/0.51  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('88', plain,
% 0.19/0.51      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.19/0.51  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('90', plain, (~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['88', '89'])).
% 0.19/0.51  thf('91', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_A)
% 0.19/0.51        | (v2_struct_0 @ sk_C_1)
% 0.19/0.51        | (r2_hidden @ sk_D @ sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['82', '90'])).
% 0.19/0.51  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('93', plain, (((r2_hidden @ sk_D @ sk_B_1) | (v2_struct_0 @ sk_C_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['91', '92'])).
% 0.19/0.51  thf('94', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('95', plain, ((r2_hidden @ sk_D @ sk_B_1)),
% 0.19/0.51      inference('clc', [status(thm)], ['93', '94'])).
% 0.19/0.51  thf('96', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['7', '95'])).
% 0.19/0.51  thf(rc6_tops_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ?[B:$i]:
% 0.19/0.51         ( ( ~( v2_tops_1 @ B @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.19/0.51           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.51  thf('97', plain,
% 0.19/0.51      (![X15 : $i]:
% 0.19/0.51         ((m1_subset_1 @ (sk_B @ X15) @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.19/0.51          | ~ (l1_pre_topc @ X15)
% 0.19/0.51          | ~ (v2_pre_topc @ X15)
% 0.19/0.51          | (v2_struct_0 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [rc6_tops_1])).
% 0.19/0.51  thf(cc1_subset_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( v1_xboole_0 @ A ) =>
% 0.19/0.51       ( ![B:$i]:
% 0.19/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.19/0.51  thf('98', plain,
% 0.19/0.51      (![X4 : $i, X5 : $i]:
% 0.19/0.51         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.19/0.51          | (v1_xboole_0 @ X4)
% 0.19/0.51          | ~ (v1_xboole_0 @ X5))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.19/0.51  thf('99', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((v2_struct_0 @ X0)
% 0.19/0.51          | ~ (v2_pre_topc @ X0)
% 0.19/0.51          | ~ (l1_pre_topc @ X0)
% 0.19/0.51          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.19/0.51          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['97', '98'])).
% 0.19/0.51  thf('100', plain,
% 0.19/0.51      (((v1_xboole_0 @ (sk_B @ sk_C_1))
% 0.19/0.51        | ~ (l1_pre_topc @ sk_C_1)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_C_1)
% 0.19/0.51        | (v2_struct_0 @ sk_C_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['96', '99'])).
% 0.19/0.51  thf('101', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(dt_m1_pre_topc, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( l1_pre_topc @ A ) =>
% 0.19/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.51  thf('102', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i]:
% 0.19/0.51         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.51          | (l1_pre_topc @ X10)
% 0.19/0.51          | ~ (l1_pre_topc @ X11))),
% 0.19/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.51  thf('103', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['101', '102'])).
% 0.19/0.51  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('105', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.51      inference('demod', [status(thm)], ['103', '104'])).
% 0.19/0.51  thf('106', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc1_pre_topc, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.19/0.51  thf('107', plain,
% 0.19/0.51      (![X8 : $i, X9 : $i]:
% 0.19/0.51         (~ (m1_pre_topc @ X8 @ X9)
% 0.19/0.51          | (v2_pre_topc @ X8)
% 0.19/0.51          | ~ (l1_pre_topc @ X9)
% 0.19/0.51          | ~ (v2_pre_topc @ X9))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.51  thf('108', plain,
% 0.19/0.51      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.51        | (v2_pre_topc @ sk_C_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['106', '107'])).
% 0.19/0.51  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('111', plain, ((v2_pre_topc @ sk_C_1)),
% 0.19/0.51      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.19/0.51  thf('112', plain,
% 0.19/0.51      (((v1_xboole_0 @ (sk_B @ sk_C_1)) | (v2_struct_0 @ sk_C_1))),
% 0.19/0.51      inference('demod', [status(thm)], ['100', '105', '111'])).
% 0.19/0.51  thf('113', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('114', plain, ((v1_xboole_0 @ (sk_B @ sk_C_1))),
% 0.19/0.51      inference('clc', [status(thm)], ['112', '113'])).
% 0.19/0.51  thf('115', plain,
% 0.19/0.51      (![X15 : $i]:
% 0.19/0.51         (~ (v1_xboole_0 @ (sk_B @ X15))
% 0.19/0.51          | ~ (l1_pre_topc @ X15)
% 0.19/0.51          | ~ (v2_pre_topc @ X15)
% 0.19/0.51          | (v2_struct_0 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [rc6_tops_1])).
% 0.19/0.51  thf('116', plain,
% 0.19/0.51      (((v2_struct_0 @ sk_C_1)
% 0.19/0.51        | ~ (v2_pre_topc @ sk_C_1)
% 0.19/0.51        | ~ (l1_pre_topc @ sk_C_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['114', '115'])).
% 0.19/0.51  thf('117', plain, ((v2_pre_topc @ sk_C_1)),
% 0.19/0.51      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.19/0.51  thf('118', plain, ((l1_pre_topc @ sk_C_1)),
% 0.19/0.51      inference('demod', [status(thm)], ['103', '104'])).
% 0.19/0.51  thf('119', plain, ((v2_struct_0 @ sk_C_1)),
% 0.19/0.51      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.19/0.51  thf('120', plain, ($false), inference('demod', [status(thm)], ['0', '119'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
