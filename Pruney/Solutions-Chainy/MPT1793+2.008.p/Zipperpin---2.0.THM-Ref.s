%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DskJZNmSPa

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:51 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 526 expanded)
%              Number of leaves         :   43 ( 167 expanded)
%              Depth                    :   25
%              Number of atoms          : 1498 (11299 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ sk_C_2 ) ) ),
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
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_D @ sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C_2 ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_C_2 @ X0 )
      | ( v2_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_C_2 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_C_2 )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_C_2 ) ),
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
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r2_hidden @ X35 @ X33 )
      | ( r1_tmap_1 @ X34 @ ( k6_tmap_1 @ X34 @ X33 ) @ ( k7_tmap_1 @ X34 @ X33 ) @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t108_tmap_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B_2 ) ) ),
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
      | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 )
      | ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_D @ sk_B_2 )
    | ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_D )
    | ( r2_hidden @ sk_D @ sk_B_2 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X30 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ) )
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
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ( r1_tmap_1 @ X37 @ X39 @ ( k2_tmap_1 @ X36 @ X39 @ X40 @ X37 ) @ X38 )
      | ( X41 != X38 )
      | ~ ( r1_tmap_1 @ X36 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X36 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('38',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X36 ) @ ( u1_struct_0 @ X39 ) ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r1_tmap_1 @ X36 @ X39 @ X40 @ X38 )
      | ( r1_tmap_1 @ X37 @ X39 @ ( k2_tmap_1 @ X36 @ X39 @ X40 @ X37 ) @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_pre_topc @ X37 @ X36 )
      | ( v2_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('44',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) )
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
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('52',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) )
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
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('60',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
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
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v2_pre_topc @ ( k6_tmap_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('68',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
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
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41','49','57','65','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B_2 )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 ) @ sk_D )
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
      ( ( r2_hidden @ sk_D @ sk_B_2 )
      | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
      | ( r1_tmap_1 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ X0 ) @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_2 )
    | ~ ( m1_pre_topc @ sk_C_2 @ sk_A )
    | ( r1_tmap_1 @ sk_C_2 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_C_2 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ sk_D @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['8','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_2 )
    | ( r1_tmap_1 @ sk_C_2 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_C_2 ) @ sk_D )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ sk_D @ sk_B_2 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( r1_tmap_1 @ sk_C_2 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k2_tmap_1 @ sk_A @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) @ ( k7_tmap_1 @ sk_A @ sk_B_2 ) @ sk_C_2 ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r2_hidden @ sk_D @ sk_B_2 )
    | ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_C_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_struct_0 @ ( k6_tmap_1 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_tmap_1])).

thf('85',plain,
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
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
    ( ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( v2_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_2 )
    | ( r2_hidden @ sk_D @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['82','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r2_hidden @ sk_D @ sk_B_2 )
    | ( v2_struct_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r2_hidden @ sk_D @ sk_B_2 ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['7','95'])).

thf('97',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['7','95'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('98',plain,(
    ! [X26: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('99',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B_1 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('101',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('104',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,
    ( ( ( sk_B_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ sk_C_2 )
    | ~ ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('109',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('110',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('115',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('116',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( sk_B_1 @ sk_C_2 )
      = ( u1_struct_0 @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['107','113','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( sk_B_1 @ sk_C_2 )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    v1_xboole_0 @ ( sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['96','121'])).

thf('123',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_C_2 )
    | ~ ( v2_pre_topc @ sk_C_2 )
    | ~ ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('126',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['116','117'])).

thf('127',plain,(
    v2_struct_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['0','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DskJZNmSPa
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:59:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.91/1.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.18  % Solved by: fo/fo7.sh
% 0.91/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.18  % done 1320 iterations in 0.721s
% 0.91/1.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.18  % SZS output start Refutation
% 0.91/1.18  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.91/1.18  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.91/1.18  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.18  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.91/1.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.18  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.18  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.91/1.18  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.91/1.18  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.18  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.18  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.18  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.18  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.91/1.18  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.91/1.18  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.91/1.18  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.91/1.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.18  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.91/1.18  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.91/1.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.18  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.91/1.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.18  thf(t109_tmap_1, conjecture,
% 0.91/1.18    (![A:$i]:
% 0.91/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.18       ( ![B:$i]:
% 0.91/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.18           ( ![C:$i]:
% 0.91/1.18             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.91/1.18               ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.91/1.18                 ( ![D:$i]:
% 0.91/1.18                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.91/1.18                     ( r1_tmap_1 @
% 0.91/1.18                       C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.91/1.18                       ( k2_tmap_1 @
% 0.91/1.18                         A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.91/1.18                       D ) ) ) ) ) ) ) ) ))).
% 0.91/1.18  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.18    (~( ![A:$i]:
% 0.91/1.18        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.91/1.18            ( l1_pre_topc @ A ) ) =>
% 0.91/1.18          ( ![B:$i]:
% 0.91/1.18            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.18              ( ![C:$i]:
% 0.91/1.18                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.91/1.18                  ( ( r1_xboole_0 @ ( u1_struct_0 @ C ) @ B ) =>
% 0.91/1.18                    ( ![D:$i]:
% 0.91/1.18                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) =>
% 0.91/1.18                        ( r1_tmap_1 @
% 0.91/1.18                          C @ ( k6_tmap_1 @ A @ B ) @ 
% 0.91/1.18                          ( k2_tmap_1 @
% 0.91/1.18                            A @ ( k6_tmap_1 @ A @ B ) @ 
% 0.91/1.18                            ( k7_tmap_1 @ A @ B ) @ C ) @ 
% 0.91/1.18                          D ) ) ) ) ) ) ) ) ) )),
% 0.91/1.18    inference('cnf.neg', [status(esa)], [t109_tmap_1])).
% 0.91/1.18  thf('0', plain, (~ (v2_struct_0 @ sk_C_2)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('1', plain, ((r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ sk_B_2)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('2', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_2))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf(t2_subset, axiom,
% 0.91/1.18    (![A:$i,B:$i]:
% 0.91/1.18     ( ( m1_subset_1 @ A @ B ) =>
% 0.91/1.18       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.91/1.18  thf('3', plain,
% 0.91/1.18      (![X14 : $i, X15 : $i]:
% 0.91/1.18         ((r2_hidden @ X14 @ X15)
% 0.91/1.18          | (v1_xboole_0 @ X15)
% 0.91/1.18          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.91/1.18      inference('cnf', [status(esa)], [t2_subset])).
% 0.91/1.18  thf('4', plain,
% 0.91/1.18      (((v1_xboole_0 @ (u1_struct_0 @ sk_C_2))
% 0.91/1.18        | (r2_hidden @ sk_D @ (u1_struct_0 @ sk_C_2)))),
% 0.91/1.18      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.18  thf(t3_xboole_0, axiom,
% 0.91/1.18    (![A:$i,B:$i]:
% 0.91/1.18     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.91/1.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.18            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.91/1.18  thf('5', plain,
% 0.91/1.18      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.91/1.18         (~ (r2_hidden @ X9 @ X7)
% 0.91/1.18          | ~ (r2_hidden @ X9 @ X10)
% 0.91/1.18          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.91/1.18      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.18  thf('6', plain,
% 0.91/1.18      (![X0 : $i]:
% 0.91/1.18         ((v1_xboole_0 @ (u1_struct_0 @ sk_C_2))
% 0.91/1.18          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ X0)
% 0.91/1.18          | ~ (r2_hidden @ sk_D @ X0))),
% 0.91/1.18      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.18  thf('7', plain,
% 0.91/1.18      ((~ (r2_hidden @ sk_D @ sk_B_2) | (v1_xboole_0 @ (u1_struct_0 @ sk_C_2)))),
% 0.91/1.18      inference('sup-', [status(thm)], ['1', '6'])).
% 0.91/1.18  thf('8', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_2))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('9', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('10', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C_2))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf(t55_pre_topc, axiom,
% 0.91/1.18    (![A:$i]:
% 0.91/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.18       ( ![B:$i]:
% 0.91/1.18         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.91/1.18           ( ![C:$i]:
% 0.91/1.18             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.91/1.18               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.91/1.18  thf('11', plain,
% 0.91/1.18      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.18         ((v2_struct_0 @ X23)
% 0.91/1.18          | ~ (m1_pre_topc @ X23 @ X24)
% 0.91/1.18          | (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.91/1.18          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 0.91/1.18          | ~ (l1_pre_topc @ X24)
% 0.91/1.18          | (v2_struct_0 @ X24))),
% 0.91/1.18      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.91/1.18  thf('12', plain,
% 0.91/1.18      (![X0 : $i]:
% 0.91/1.18         ((v2_struct_0 @ X0)
% 0.91/1.18          | ~ (l1_pre_topc @ X0)
% 0.91/1.18          | (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.91/1.18          | ~ (m1_pre_topc @ sk_C_2 @ X0)
% 0.91/1.18          | (v2_struct_0 @ sk_C_2))),
% 0.91/1.18      inference('sup-', [status(thm)], ['10', '11'])).
% 0.91/1.18  thf('13', plain,
% 0.91/1.18      (((v2_struct_0 @ sk_C_2)
% 0.91/1.18        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.91/1.18        | ~ (l1_pre_topc @ sk_A)
% 0.91/1.18        | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('sup-', [status(thm)], ['9', '12'])).
% 0.91/1.18  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('15', plain,
% 0.91/1.18      (((v2_struct_0 @ sk_C_2)
% 0.91/1.18        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.91/1.18        | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('demod', [status(thm)], ['13', '14'])).
% 0.91/1.18  thf('16', plain, (~ (v2_struct_0 @ sk_C_2)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('17', plain,
% 0.91/1.18      (((v2_struct_0 @ sk_A) | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A)))),
% 0.91/1.18      inference('clc', [status(thm)], ['15', '16'])).
% 0.91/1.18  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('19', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.91/1.18      inference('clc', [status(thm)], ['17', '18'])).
% 0.91/1.18  thf('20', plain,
% 0.91/1.18      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf(t108_tmap_1, axiom,
% 0.91/1.18    (![A:$i]:
% 0.91/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.18       ( ![B:$i]:
% 0.91/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.18           ( ![C:$i]:
% 0.91/1.18             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.18               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.91/1.18                 ( r1_tmap_1 @
% 0.91/1.18                   A @ ( k6_tmap_1 @ A @ B ) @ ( k7_tmap_1 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.91/1.18  thf('21', plain,
% 0.91/1.18      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.91/1.18         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.91/1.18          | (r2_hidden @ X35 @ X33)
% 0.91/1.18          | (r1_tmap_1 @ X34 @ (k6_tmap_1 @ X34 @ X33) @ 
% 0.91/1.18             (k7_tmap_1 @ X34 @ X33) @ X35)
% 0.91/1.18          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 0.91/1.18          | ~ (l1_pre_topc @ X34)
% 0.91/1.18          | ~ (v2_pre_topc @ X34)
% 0.91/1.18          | (v2_struct_0 @ X34))),
% 0.91/1.18      inference('cnf', [status(esa)], [t108_tmap_1])).
% 0.91/1.18  thf('22', plain,
% 0.91/1.18      (![X0 : $i]:
% 0.91/1.18         ((v2_struct_0 @ sk_A)
% 0.91/1.18          | ~ (v2_pre_topc @ sk_A)
% 0.91/1.18          | ~ (l1_pre_topc @ sk_A)
% 0.91/1.18          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.18          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18             (k7_tmap_1 @ sk_A @ sk_B_2) @ X0)
% 0.91/1.18          | (r2_hidden @ X0 @ sk_B_2))),
% 0.91/1.18      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.18  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('25', plain,
% 0.91/1.18      (![X0 : $i]:
% 0.91/1.18         ((v2_struct_0 @ sk_A)
% 0.91/1.18          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.91/1.18          | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18             (k7_tmap_1 @ sk_A @ sk_B_2) @ X0)
% 0.91/1.18          | (r2_hidden @ X0 @ sk_B_2))),
% 0.91/1.18      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.91/1.18  thf('26', plain,
% 0.91/1.18      (((r2_hidden @ sk_D @ sk_B_2)
% 0.91/1.18        | (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18           (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_D)
% 0.91/1.18        | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('sup-', [status(thm)], ['19', '25'])).
% 0.91/1.18  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('28', plain,
% 0.91/1.18      (((r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18         (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_D)
% 0.91/1.18        | (r2_hidden @ sk_D @ sk_B_2))),
% 0.91/1.18      inference('clc', [status(thm)], ['26', '27'])).
% 0.91/1.18  thf('29', plain,
% 0.91/1.18      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf(dt_k7_tmap_1, axiom,
% 0.91/1.18    (![A:$i,B:$i]:
% 0.91/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.91/1.18         ( l1_pre_topc @ A ) & 
% 0.91/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.18       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.91/1.18         ( v1_funct_2 @
% 0.91/1.18           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.91/1.18           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.91/1.18         ( m1_subset_1 @
% 0.91/1.18           ( k7_tmap_1 @ A @ B ) @ 
% 0.91/1.18           ( k1_zfmisc_1 @
% 0.91/1.18             ( k2_zfmisc_1 @
% 0.91/1.18               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.91/1.18  thf('30', plain,
% 0.91/1.18      (![X29 : $i, X30 : $i]:
% 0.91/1.18         (~ (l1_pre_topc @ X29)
% 0.91/1.18          | ~ (v2_pre_topc @ X29)
% 0.91/1.18          | (v2_struct_0 @ X29)
% 0.91/1.18          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.91/1.18          | (m1_subset_1 @ (k7_tmap_1 @ X29 @ X30) @ 
% 0.91/1.18             (k1_zfmisc_1 @ 
% 0.91/1.18              (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ 
% 0.91/1.18               (u1_struct_0 @ (k6_tmap_1 @ X29 @ X30))))))),
% 0.91/1.18      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.91/1.18  thf('31', plain,
% 0.91/1.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18         (k1_zfmisc_1 @ 
% 0.91/1.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))))
% 0.91/1.18        | (v2_struct_0 @ sk_A)
% 0.91/1.18        | ~ (v2_pre_topc @ sk_A)
% 0.91/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.18      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.18  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('34', plain,
% 0.91/1.18      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18         (k1_zfmisc_1 @ 
% 0.91/1.18          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.18           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))))
% 0.91/1.18        | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.91/1.18  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('36', plain,
% 0.91/1.18      ((m1_subset_1 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18        (k1_zfmisc_1 @ 
% 0.91/1.18         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.18          (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))))),
% 0.91/1.18      inference('clc', [status(thm)], ['34', '35'])).
% 0.91/1.18  thf(t64_tmap_1, axiom,
% 0.91/1.18    (![A:$i]:
% 0.91/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.18       ( ![B:$i]:
% 0.91/1.18         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.91/1.18             ( l1_pre_topc @ B ) ) =>
% 0.91/1.18           ( ![C:$i]:
% 0.91/1.18             ( ( ( v1_funct_1 @ C ) & 
% 0.91/1.18                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.91/1.18                 ( m1_subset_1 @
% 0.91/1.18                   C @ 
% 0.91/1.18                   ( k1_zfmisc_1 @
% 0.91/1.18                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.91/1.18               ( ![D:$i]:
% 0.91/1.18                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.91/1.18                   ( ![E:$i]:
% 0.91/1.18                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.91/1.18                       ( ![F:$i]:
% 0.91/1.18                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.91/1.18                           ( ( ( ( E ) = ( F ) ) & 
% 0.91/1.18                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.91/1.18                             ( r1_tmap_1 @
% 0.91/1.18                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.18  thf('37', plain,
% 0.91/1.18      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.91/1.18         ((v2_struct_0 @ X36)
% 0.91/1.18          | ~ (v2_pre_topc @ X36)
% 0.91/1.18          | ~ (l1_pre_topc @ X36)
% 0.91/1.18          | (v2_struct_0 @ X37)
% 0.91/1.18          | ~ (m1_pre_topc @ X37 @ X36)
% 0.91/1.18          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 0.91/1.18          | (r1_tmap_1 @ X37 @ X39 @ (k2_tmap_1 @ X36 @ X39 @ X40 @ X37) @ X38)
% 0.91/1.18          | ((X41) != (X38))
% 0.91/1.18          | ~ (r1_tmap_1 @ X36 @ X39 @ X40 @ X41)
% 0.91/1.18          | ~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X36))
% 0.91/1.18          | ~ (m1_subset_1 @ X40 @ 
% 0.91/1.18               (k1_zfmisc_1 @ 
% 0.91/1.18                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X39))))
% 0.91/1.18          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X39))
% 0.91/1.18          | ~ (v1_funct_1 @ X40)
% 0.91/1.18          | ~ (l1_pre_topc @ X39)
% 0.91/1.18          | ~ (v2_pre_topc @ X39)
% 0.91/1.18          | (v2_struct_0 @ X39))),
% 0.91/1.18      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.91/1.18  thf('38', plain,
% 0.91/1.18      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.91/1.18         ((v2_struct_0 @ X39)
% 0.91/1.18          | ~ (v2_pre_topc @ X39)
% 0.91/1.18          | ~ (l1_pre_topc @ X39)
% 0.91/1.18          | ~ (v1_funct_1 @ X40)
% 0.91/1.18          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X39))
% 0.91/1.18          | ~ (m1_subset_1 @ X40 @ 
% 0.91/1.18               (k1_zfmisc_1 @ 
% 0.91/1.18                (k2_zfmisc_1 @ (u1_struct_0 @ X36) @ (u1_struct_0 @ X39))))
% 0.91/1.18          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X36))
% 0.91/1.18          | ~ (r1_tmap_1 @ X36 @ X39 @ X40 @ X38)
% 0.91/1.18          | (r1_tmap_1 @ X37 @ X39 @ (k2_tmap_1 @ X36 @ X39 @ X40 @ X37) @ X38)
% 0.91/1.18          | ~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X37))
% 0.91/1.18          | ~ (m1_pre_topc @ X37 @ X36)
% 0.91/1.18          | (v2_struct_0 @ X37)
% 0.91/1.18          | ~ (l1_pre_topc @ X36)
% 0.91/1.18          | ~ (v2_pre_topc @ X36)
% 0.91/1.18          | (v2_struct_0 @ X36))),
% 0.91/1.18      inference('simplify', [status(thm)], ['37'])).
% 0.91/1.18  thf('39', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]:
% 0.91/1.18         ((v2_struct_0 @ sk_A)
% 0.91/1.18          | ~ (v2_pre_topc @ sk_A)
% 0.91/1.18          | ~ (l1_pre_topc @ sk_A)
% 0.91/1.18          | (v2_struct_0 @ X0)
% 0.91/1.18          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.91/1.18          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.91/1.18          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18              (k7_tmap_1 @ sk_A @ sk_B_2) @ X0) @ 
% 0.91/1.18             X1)
% 0.91/1.18          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18               (k7_tmap_1 @ sk_A @ sk_B_2) @ X1)
% 0.91/1.18          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.91/1.18          | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18               (u1_struct_0 @ sk_A) @ 
% 0.91/1.18               (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.91/1.18          | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18          | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))),
% 0.91/1.18      inference('sup-', [status(thm)], ['36', '38'])).
% 0.91/1.18  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('42', plain,
% 0.91/1.18      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('43', plain,
% 0.91/1.18      (![X29 : $i, X30 : $i]:
% 0.91/1.18         (~ (l1_pre_topc @ X29)
% 0.91/1.18          | ~ (v2_pre_topc @ X29)
% 0.91/1.18          | (v2_struct_0 @ X29)
% 0.91/1.18          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.91/1.18          | (v1_funct_2 @ (k7_tmap_1 @ X29 @ X30) @ (u1_struct_0 @ X29) @ 
% 0.91/1.18             (u1_struct_0 @ (k6_tmap_1 @ X29 @ X30))))),
% 0.91/1.18      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.91/1.18  thf('44', plain,
% 0.91/1.18      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.18         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.91/1.18        | (v2_struct_0 @ sk_A)
% 0.91/1.18        | ~ (v2_pre_topc @ sk_A)
% 0.91/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.18      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.18  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('47', plain,
% 0.91/1.18      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.18         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))
% 0.91/1.18        | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.91/1.18  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('49', plain,
% 0.91/1.18      ((v1_funct_2 @ (k7_tmap_1 @ sk_A @ sk_B_2) @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.18        (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))),
% 0.91/1.18      inference('clc', [status(thm)], ['47', '48'])).
% 0.91/1.18  thf('50', plain,
% 0.91/1.18      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('51', plain,
% 0.91/1.18      (![X29 : $i, X30 : $i]:
% 0.91/1.18         (~ (l1_pre_topc @ X29)
% 0.91/1.18          | ~ (v2_pre_topc @ X29)
% 0.91/1.18          | (v2_struct_0 @ X29)
% 0.91/1.18          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.91/1.18          | (v1_funct_1 @ (k7_tmap_1 @ X29 @ X30)))),
% 0.91/1.18      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.91/1.18  thf('52', plain,
% 0.91/1.18      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18        | (v2_struct_0 @ sk_A)
% 0.91/1.18        | ~ (v2_pre_topc @ sk_A)
% 0.91/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.18      inference('sup-', [status(thm)], ['50', '51'])).
% 0.91/1.18  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('55', plain,
% 0.91/1.18      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.91/1.18  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('57', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ sk_B_2))),
% 0.91/1.18      inference('clc', [status(thm)], ['55', '56'])).
% 0.91/1.18  thf('58', plain,
% 0.91/1.18      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf(dt_k6_tmap_1, axiom,
% 0.91/1.18    (![A:$i,B:$i]:
% 0.91/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.91/1.18         ( l1_pre_topc @ A ) & 
% 0.91/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.18       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.91/1.18         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.91/1.18         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.91/1.18  thf('59', plain,
% 0.91/1.18      (![X27 : $i, X28 : $i]:
% 0.91/1.18         (~ (l1_pre_topc @ X27)
% 0.91/1.18          | ~ (v2_pre_topc @ X27)
% 0.91/1.18          | (v2_struct_0 @ X27)
% 0.91/1.18          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.91/1.18          | (l1_pre_topc @ (k6_tmap_1 @ X27 @ X28)))),
% 0.91/1.18      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.91/1.18  thf('60', plain,
% 0.91/1.18      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18        | (v2_struct_0 @ sk_A)
% 0.91/1.18        | ~ (v2_pre_topc @ sk_A)
% 0.91/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.18      inference('sup-', [status(thm)], ['58', '59'])).
% 0.91/1.18  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('63', plain,
% 0.91/1.18      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.91/1.18  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('65', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))),
% 0.91/1.18      inference('clc', [status(thm)], ['63', '64'])).
% 0.91/1.18  thf('66', plain,
% 0.91/1.18      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('67', plain,
% 0.91/1.18      (![X27 : $i, X28 : $i]:
% 0.91/1.18         (~ (l1_pre_topc @ X27)
% 0.91/1.18          | ~ (v2_pre_topc @ X27)
% 0.91/1.18          | (v2_struct_0 @ X27)
% 0.91/1.18          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.91/1.18          | (v2_pre_topc @ (k6_tmap_1 @ X27 @ X28)))),
% 0.91/1.18      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.91/1.18  thf('68', plain,
% 0.91/1.18      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18        | (v2_struct_0 @ sk_A)
% 0.91/1.18        | ~ (v2_pre_topc @ sk_A)
% 0.91/1.18        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.18      inference('sup-', [status(thm)], ['66', '67'])).
% 0.91/1.18  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('71', plain,
% 0.91/1.18      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.91/1.18  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('73', plain, ((v2_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B_2))),
% 0.91/1.18      inference('clc', [status(thm)], ['71', '72'])).
% 0.91/1.18  thf('74', plain,
% 0.91/1.18      (![X0 : $i, X1 : $i]:
% 0.91/1.18         ((v2_struct_0 @ sk_A)
% 0.91/1.18          | (v2_struct_0 @ X0)
% 0.91/1.18          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.91/1.18          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.91/1.18          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18              (k7_tmap_1 @ sk_A @ sk_B_2) @ X0) @ 
% 0.91/1.18             X1)
% 0.91/1.18          | ~ (r1_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18               (k7_tmap_1 @ sk_A @ sk_B_2) @ X1)
% 0.91/1.18          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.91/1.18          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)))),
% 0.91/1.18      inference('demod', [status(thm)],
% 0.91/1.18                ['39', '40', '41', '49', '57', '65', '73'])).
% 0.91/1.18  thf('75', plain,
% 0.91/1.18      (![X0 : $i]:
% 0.91/1.18         ((r2_hidden @ sk_D @ sk_B_2)
% 0.91/1.18          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))
% 0.91/1.18          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18              (k7_tmap_1 @ sk_A @ sk_B_2) @ X0) @ 
% 0.91/1.18             sk_D)
% 0.91/1.18          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.91/1.18          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.91/1.18          | (v2_struct_0 @ X0)
% 0.91/1.18          | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('sup-', [status(thm)], ['28', '74'])).
% 0.91/1.18  thf('76', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.91/1.18      inference('clc', [status(thm)], ['17', '18'])).
% 0.91/1.18  thf('77', plain,
% 0.91/1.18      (![X0 : $i]:
% 0.91/1.18         ((r2_hidden @ sk_D @ sk_B_2)
% 0.91/1.18          | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18          | (r1_tmap_1 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18             (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18              (k7_tmap_1 @ sk_A @ sk_B_2) @ X0) @ 
% 0.91/1.18             sk_D)
% 0.91/1.18          | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ X0))
% 0.91/1.18          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.91/1.18          | (v2_struct_0 @ X0)
% 0.91/1.18          | (v2_struct_0 @ sk_A))),
% 0.91/1.18      inference('demod', [status(thm)], ['75', '76'])).
% 0.91/1.18  thf('78', plain,
% 0.91/1.18      (((v2_struct_0 @ sk_A)
% 0.91/1.18        | (v2_struct_0 @ sk_C_2)
% 0.91/1.18        | ~ (m1_pre_topc @ sk_C_2 @ sk_A)
% 0.91/1.18        | (r1_tmap_1 @ sk_C_2 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18            (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_C_2) @ 
% 0.91/1.18           sk_D)
% 0.91/1.18        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18        | (r2_hidden @ sk_D @ sk_B_2))),
% 0.91/1.18      inference('sup-', [status(thm)], ['8', '77'])).
% 0.91/1.18  thf('79', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.18  thf('80', plain,
% 0.91/1.18      (((v2_struct_0 @ sk_A)
% 0.91/1.18        | (v2_struct_0 @ sk_C_2)
% 0.91/1.18        | (r1_tmap_1 @ sk_C_2 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18           (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18            (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_C_2) @ 
% 0.91/1.18           sk_D)
% 0.91/1.18        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 0.91/1.18        | (r2_hidden @ sk_D @ sk_B_2))),
% 0.91/1.18      inference('demod', [status(thm)], ['78', '79'])).
% 0.91/1.18  thf('81', plain,
% 0.91/1.18      (~ (r1_tmap_1 @ sk_C_2 @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18          (k2_tmap_1 @ sk_A @ (k6_tmap_1 @ sk_A @ sk_B_2) @ 
% 0.91/1.18           (k7_tmap_1 @ sk_A @ sk_B_2) @ sk_C_2) @ 
% 0.91/1.18          sk_D)),
% 0.91/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('82', plain,
% 1.03/1.18      (((r2_hidden @ sk_D @ sk_B_2)
% 1.03/1.18        | (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 1.03/1.18        | (v2_struct_0 @ sk_C_2)
% 1.03/1.18        | (v2_struct_0 @ sk_A))),
% 1.03/1.18      inference('sup-', [status(thm)], ['80', '81'])).
% 1.03/1.18  thf('83', plain,
% 1.03/1.18      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf(fc4_tmap_1, axiom,
% 1.03/1.18    (![A:$i,B:$i]:
% 1.03/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.03/1.18         ( l1_pre_topc @ A ) & 
% 1.03/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.03/1.18       ( ( ~( v2_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 1.03/1.18         ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 1.03/1.18         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 1.03/1.18  thf('84', plain,
% 1.03/1.18      (![X31 : $i, X32 : $i]:
% 1.03/1.18         (~ (l1_pre_topc @ X31)
% 1.03/1.18          | ~ (v2_pre_topc @ X31)
% 1.03/1.18          | (v2_struct_0 @ X31)
% 1.03/1.18          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.03/1.18          | ~ (v2_struct_0 @ (k6_tmap_1 @ X31 @ X32)))),
% 1.03/1.18      inference('cnf', [status(esa)], [fc4_tmap_1])).
% 1.03/1.18  thf('85', plain,
% 1.03/1.18      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))
% 1.03/1.18        | (v2_struct_0 @ sk_A)
% 1.03/1.18        | ~ (v2_pre_topc @ sk_A)
% 1.03/1.18        | ~ (l1_pre_topc @ sk_A))),
% 1.03/1.18      inference('sup-', [status(thm)], ['83', '84'])).
% 1.03/1.18  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('88', plain,
% 1.03/1.18      ((~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 1.03/1.18      inference('demod', [status(thm)], ['85', '86', '87'])).
% 1.03/1.18  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('90', plain, (~ (v2_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B_2))),
% 1.03/1.18      inference('clc', [status(thm)], ['88', '89'])).
% 1.03/1.18  thf('91', plain,
% 1.03/1.18      (((v2_struct_0 @ sk_A)
% 1.03/1.18        | (v2_struct_0 @ sk_C_2)
% 1.03/1.18        | (r2_hidden @ sk_D @ sk_B_2))),
% 1.03/1.18      inference('sup-', [status(thm)], ['82', '90'])).
% 1.03/1.18  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('93', plain, (((r2_hidden @ sk_D @ sk_B_2) | (v2_struct_0 @ sk_C_2))),
% 1.03/1.18      inference('clc', [status(thm)], ['91', '92'])).
% 1.03/1.18  thf('94', plain, (~ (v2_struct_0 @ sk_C_2)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('95', plain, ((r2_hidden @ sk_D @ sk_B_2)),
% 1.03/1.18      inference('clc', [status(thm)], ['93', '94'])).
% 1.03/1.18  thf('96', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C_2))),
% 1.03/1.18      inference('demod', [status(thm)], ['7', '95'])).
% 1.03/1.18  thf('97', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_C_2))),
% 1.03/1.18      inference('demod', [status(thm)], ['7', '95'])).
% 1.03/1.18  thf(rc3_tops_1, axiom,
% 1.03/1.18    (![A:$i]:
% 1.03/1.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.03/1.18       ( ?[B:$i]:
% 1.03/1.18         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 1.03/1.18           ( ~( v1_xboole_0 @ B ) ) & 
% 1.03/1.18           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.03/1.18  thf('98', plain,
% 1.03/1.18      (![X26 : $i]:
% 1.03/1.18         ((m1_subset_1 @ (sk_B_1 @ X26) @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.03/1.18          | ~ (l1_pre_topc @ X26)
% 1.03/1.18          | ~ (v2_pre_topc @ X26)
% 1.03/1.18          | (v2_struct_0 @ X26))),
% 1.03/1.18      inference('cnf', [status(esa)], [rc3_tops_1])).
% 1.03/1.18  thf(t3_subset, axiom,
% 1.03/1.18    (![A:$i,B:$i]:
% 1.03/1.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.03/1.18  thf('99', plain,
% 1.03/1.18      (![X16 : $i, X17 : $i]:
% 1.03/1.18         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.03/1.18      inference('cnf', [status(esa)], [t3_subset])).
% 1.03/1.18  thf('100', plain,
% 1.03/1.18      (![X0 : $i]:
% 1.03/1.18         ((v2_struct_0 @ X0)
% 1.03/1.18          | ~ (v2_pre_topc @ X0)
% 1.03/1.18          | ~ (l1_pre_topc @ X0)
% 1.03/1.18          | (r1_tarski @ (sk_B_1 @ X0) @ (u1_struct_0 @ X0)))),
% 1.03/1.18      inference('sup-', [status(thm)], ['98', '99'])).
% 1.03/1.18  thf(d3_tarski, axiom,
% 1.03/1.18    (![A:$i,B:$i]:
% 1.03/1.18     ( ( r1_tarski @ A @ B ) <=>
% 1.03/1.18       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.03/1.18  thf('101', plain,
% 1.03/1.18      (![X4 : $i, X6 : $i]:
% 1.03/1.18         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.03/1.18      inference('cnf', [status(esa)], [d3_tarski])).
% 1.03/1.18  thf(d1_xboole_0, axiom,
% 1.03/1.18    (![A:$i]:
% 1.03/1.18     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.03/1.18  thf('102', plain,
% 1.03/1.18      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.03/1.18      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.03/1.18  thf('103', plain,
% 1.03/1.18      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.18      inference('sup-', [status(thm)], ['101', '102'])).
% 1.03/1.18  thf(d10_xboole_0, axiom,
% 1.03/1.18    (![A:$i,B:$i]:
% 1.03/1.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.03/1.18  thf('104', plain,
% 1.03/1.18      (![X11 : $i, X13 : $i]:
% 1.03/1.18         (((X11) = (X13))
% 1.03/1.18          | ~ (r1_tarski @ X13 @ X11)
% 1.03/1.18          | ~ (r1_tarski @ X11 @ X13))),
% 1.03/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.03/1.18  thf('105', plain,
% 1.03/1.18      (![X0 : $i, X1 : $i]:
% 1.03/1.18         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.03/1.18      inference('sup-', [status(thm)], ['103', '104'])).
% 1.03/1.18  thf('106', plain,
% 1.03/1.18      (![X0 : $i]:
% 1.03/1.18         (~ (l1_pre_topc @ X0)
% 1.03/1.18          | ~ (v2_pre_topc @ X0)
% 1.03/1.18          | (v2_struct_0 @ X0)
% 1.03/1.18          | ((sk_B_1 @ X0) = (u1_struct_0 @ X0))
% 1.03/1.18          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.03/1.18      inference('sup-', [status(thm)], ['100', '105'])).
% 1.03/1.18  thf('107', plain,
% 1.03/1.18      ((((sk_B_1 @ sk_C_2) = (u1_struct_0 @ sk_C_2))
% 1.03/1.18        | (v2_struct_0 @ sk_C_2)
% 1.03/1.18        | ~ (v2_pre_topc @ sk_C_2)
% 1.03/1.18        | ~ (l1_pre_topc @ sk_C_2))),
% 1.03/1.18      inference('sup-', [status(thm)], ['97', '106'])).
% 1.03/1.18  thf('108', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf(cc1_pre_topc, axiom,
% 1.03/1.18    (![A:$i]:
% 1.03/1.18     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.03/1.18       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 1.03/1.18  thf('109', plain,
% 1.03/1.18      (![X19 : $i, X20 : $i]:
% 1.03/1.18         (~ (m1_pre_topc @ X19 @ X20)
% 1.03/1.18          | (v2_pre_topc @ X19)
% 1.03/1.18          | ~ (l1_pre_topc @ X20)
% 1.03/1.18          | ~ (v2_pre_topc @ X20))),
% 1.03/1.18      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 1.03/1.18  thf('110', plain,
% 1.03/1.18      ((~ (v2_pre_topc @ sk_A)
% 1.03/1.18        | ~ (l1_pre_topc @ sk_A)
% 1.03/1.18        | (v2_pre_topc @ sk_C_2))),
% 1.03/1.18      inference('sup-', [status(thm)], ['108', '109'])).
% 1.03/1.18  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('113', plain, ((v2_pre_topc @ sk_C_2)),
% 1.03/1.18      inference('demod', [status(thm)], ['110', '111', '112'])).
% 1.03/1.18  thf('114', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf(dt_m1_pre_topc, axiom,
% 1.03/1.18    (![A:$i]:
% 1.03/1.18     ( ( l1_pre_topc @ A ) =>
% 1.03/1.18       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.03/1.18  thf('115', plain,
% 1.03/1.18      (![X21 : $i, X22 : $i]:
% 1.03/1.18         (~ (m1_pre_topc @ X21 @ X22)
% 1.03/1.18          | (l1_pre_topc @ X21)
% 1.03/1.18          | ~ (l1_pre_topc @ X22))),
% 1.03/1.18      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.03/1.18  thf('116', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 1.03/1.18      inference('sup-', [status(thm)], ['114', '115'])).
% 1.03/1.18  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('118', plain, ((l1_pre_topc @ sk_C_2)),
% 1.03/1.18      inference('demod', [status(thm)], ['116', '117'])).
% 1.03/1.18  thf('119', plain,
% 1.03/1.18      ((((sk_B_1 @ sk_C_2) = (u1_struct_0 @ sk_C_2)) | (v2_struct_0 @ sk_C_2))),
% 1.03/1.18      inference('demod', [status(thm)], ['107', '113', '118'])).
% 1.03/1.18  thf('120', plain, (~ (v2_struct_0 @ sk_C_2)),
% 1.03/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.18  thf('121', plain, (((sk_B_1 @ sk_C_2) = (u1_struct_0 @ sk_C_2))),
% 1.03/1.18      inference('clc', [status(thm)], ['119', '120'])).
% 1.03/1.18  thf('122', plain, ((v1_xboole_0 @ (sk_B_1 @ sk_C_2))),
% 1.03/1.18      inference('demod', [status(thm)], ['96', '121'])).
% 1.03/1.18  thf('123', plain,
% 1.03/1.18      (![X26 : $i]:
% 1.03/1.18         (~ (v1_xboole_0 @ (sk_B_1 @ X26))
% 1.03/1.18          | ~ (l1_pre_topc @ X26)
% 1.03/1.18          | ~ (v2_pre_topc @ X26)
% 1.03/1.18          | (v2_struct_0 @ X26))),
% 1.03/1.18      inference('cnf', [status(esa)], [rc3_tops_1])).
% 1.03/1.18  thf('124', plain,
% 1.03/1.18      (((v2_struct_0 @ sk_C_2)
% 1.03/1.18        | ~ (v2_pre_topc @ sk_C_2)
% 1.03/1.18        | ~ (l1_pre_topc @ sk_C_2))),
% 1.03/1.18      inference('sup-', [status(thm)], ['122', '123'])).
% 1.03/1.18  thf('125', plain, ((v2_pre_topc @ sk_C_2)),
% 1.03/1.18      inference('demod', [status(thm)], ['110', '111', '112'])).
% 1.03/1.18  thf('126', plain, ((l1_pre_topc @ sk_C_2)),
% 1.03/1.18      inference('demod', [status(thm)], ['116', '117'])).
% 1.03/1.18  thf('127', plain, ((v2_struct_0 @ sk_C_2)),
% 1.03/1.18      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.03/1.18  thf('128', plain, ($false), inference('demod', [status(thm)], ['0', '127'])).
% 1.03/1.18  
% 1.03/1.18  % SZS output end Refutation
% 1.03/1.18  
% 1.03/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
