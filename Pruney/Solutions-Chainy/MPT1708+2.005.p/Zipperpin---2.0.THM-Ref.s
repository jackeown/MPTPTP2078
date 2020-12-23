%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H8EOcMNDeo

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:13 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 314 expanded)
%              Number of leaves         :   32 (  99 expanded)
%              Depth                    :   33
%              Number of atoms          : 1533 (6621 expanded)
%              Number of equality atoms :   35 ( 252 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t17_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                   => ( ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                      & ? [E: $i] :
                          ( ( E = D )
                          & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ~ ( r1_tsep_1 @ B @ C )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) )
                     => ( ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
                        & ? [E: $i] :
                            ( ( E = D )
                            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_pre_topc @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( D
                        = ( k2_tsep_1 @ A @ B @ C ) )
                    <=> ( ( u1_struct_0 @ D )
                        = ( k3_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( r1_tsep_1 @ X26 @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( v1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X27 )
      | ( X29
       != ( k2_tsep_1 @ X27 @ X26 @ X28 ) )
      | ( ( u1_struct_0 @ X29 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X27 @ X26 @ X28 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X27 @ X26 @ X28 ) @ X27 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X27 @ X26 @ X28 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X27 @ X26 @ X28 ) )
      | ( r1_tsep_1 @ X26 @ X28 )
      | ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('50',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('55',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) )
      | ( X33 != sk_D_1 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( X34 != sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ! [X34: $i] :
        ( ( X34 != sk_D_1 )
        | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ! [X34: $i] :
        ( ( X34 != sk_D_1 )
        | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) )
   <= ! [X34: $i] :
        ( ( X34 != sk_D_1 )
        | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('70',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('72',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('78',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_pre_topc @ X32 @ X31 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X31 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['66'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C_1 ) )
   <= ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C_1 ) )
   <= ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ~ ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ! [X34: $i] :
        ( ( X34 != sk_D_1 )
        | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ! [X33: $i] :
        ( ( X33 != sk_D_1 )
        | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['66'])).

thf('100',plain,(
    ! [X34: $i] :
      ( ( X34 != sk_D_1 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['68','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','101'])).

thf('103',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v2_struct_0 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['0','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H8EOcMNDeo
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 388 iterations in 0.338s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.80  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.80  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.58/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.58/0.80  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.80  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.58/0.80  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.58/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.80  thf(t17_tmap_1, conjecture,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.80               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.58/0.80                 ( ![D:$i]:
% 0.58/0.80                   ( ( m1_subset_1 @
% 0.58/0.80                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.58/0.80                     ( ( ?[E:$i]:
% 0.58/0.80                         ( ( ( E ) = ( D ) ) & 
% 0.58/0.80                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.58/0.80                       ( ?[E:$i]:
% 0.58/0.80                         ( ( ( E ) = ( D ) ) & 
% 0.58/0.80                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i]:
% 0.58/0.80        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.80            ( l1_pre_topc @ A ) ) =>
% 0.58/0.80          ( ![B:$i]:
% 0.58/0.80            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.58/0.80              ( ![C:$i]:
% 0.58/0.80                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.80                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.58/0.80                    ( ![D:$i]:
% 0.58/0.80                      ( ( m1_subset_1 @
% 0.58/0.80                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.58/0.80                        ( ( ?[E:$i]:
% 0.58/0.80                            ( ( ( E ) = ( D ) ) & 
% 0.58/0.80                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.58/0.80                          ( ?[E:$i]:
% 0.58/0.80                            ( ( ( E ) = ( D ) ) & 
% 0.58/0.80                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 0.58/0.80  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('1', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(dt_k2_tsep_1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.58/0.80         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.58/0.80         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.80       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 0.58/0.80         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 0.58/0.80         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X30 @ X31)
% 0.58/0.80          | (v2_struct_0 @ X30)
% 0.58/0.80          | ~ (l1_pre_topc @ X31)
% 0.58/0.80          | (v2_struct_0 @ X31)
% 0.58/0.80          | (v2_struct_0 @ X32)
% 0.58/0.80          | ~ (m1_pre_topc @ X32 @ X31)
% 0.58/0.80          | (m1_pre_topc @ (k2_tsep_1 @ X31 @ X30 @ X32) @ X31))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.58/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ X0)
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ sk_B))),
% 0.58/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.80  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.58/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ X0)
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ sk_B))),
% 0.58/0.80      inference('demod', [status(thm)], ['4', '5'])).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_B)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_C_1)
% 0.58/0.80        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['1', '6'])).
% 0.58/0.80  thf(dt_m1_pre_topc, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( l1_pre_topc @ A ) =>
% 0.58/0.80       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X23 : $i, X24 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X23 @ X24)
% 0.58/0.80          | (l1_pre_topc @ X23)
% 0.58/0.80          | ~ (l1_pre_topc @ X24))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_C_1)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_B)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.80  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_C_1)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_B)
% 0.58/0.80        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.80      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.80  thf(dt_l1_pre_topc, axiom,
% 0.58/0.80    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_B)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_C_1)
% 0.58/0.80        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.80  thf('14', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         (~ (m1_pre_topc @ X30 @ X31)
% 0.58/0.80          | (v2_struct_0 @ X30)
% 0.58/0.80          | ~ (l1_pre_topc @ X31)
% 0.58/0.80          | (v2_struct_0 @ X31)
% 0.58/0.80          | (v2_struct_0 @ X32)
% 0.58/0.80          | ~ (m1_pre_topc @ X32 @ X31)
% 0.58/0.80          | (v1_pre_topc @ (k2_tsep_1 @ X31 @ X30 @ X32)))),
% 0.58/0.80      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.58/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ X0)
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ sk_B))),
% 0.58/0.80      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.80  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('19', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.58/0.80          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ X0)
% 0.58/0.80          | (v2_struct_0 @ sk_A)
% 0.58/0.80          | (v2_struct_0 @ sk_B))),
% 0.58/0.80      inference('demod', [status(thm)], ['17', '18'])).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_B)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_C_1)
% 0.58/0.80        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.80      inference('sup-', [status(thm)], ['14', '19'])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_B)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_C_1)
% 0.58/0.80        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['1', '6'])).
% 0.58/0.80  thf(d5_tsep_1, axiom,
% 0.58/0.80    (![A:$i]:
% 0.58/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.80       ( ![B:$i]:
% 0.58/0.80         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.58/0.80           ( ![C:$i]:
% 0.58/0.80             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.80               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.58/0.80                 ( ![D:$i]:
% 0.58/0.80                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.58/0.80                       ( m1_pre_topc @ D @ A ) ) =>
% 0.58/0.80                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 0.58/0.80                       ( ( u1_struct_0 @ D ) =
% 0.58/0.80                         ( k3_xboole_0 @
% 0.58/0.80                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.58/0.80  thf('22', plain,
% 0.58/0.80      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.58/0.80         ((v2_struct_0 @ X26)
% 0.58/0.80          | ~ (m1_pre_topc @ X26 @ X27)
% 0.58/0.80          | (r1_tsep_1 @ X26 @ X28)
% 0.58/0.80          | (v2_struct_0 @ X29)
% 0.58/0.80          | ~ (v1_pre_topc @ X29)
% 0.58/0.80          | ~ (m1_pre_topc @ X29 @ X27)
% 0.58/0.80          | ((X29) != (k2_tsep_1 @ X27 @ X26 @ X28))
% 0.58/0.80          | ((u1_struct_0 @ X29)
% 0.58/0.80              = (k3_xboole_0 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X28)))
% 0.58/0.80          | ~ (m1_pre_topc @ X28 @ X27)
% 0.58/0.80          | (v2_struct_0 @ X28)
% 0.58/0.80          | ~ (l1_pre_topc @ X27)
% 0.58/0.80          | (v2_struct_0 @ X27))),
% 0.58/0.80      inference('cnf', [status(esa)], [d5_tsep_1])).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.58/0.80         ((v2_struct_0 @ X27)
% 0.58/0.80          | ~ (l1_pre_topc @ X27)
% 0.58/0.80          | (v2_struct_0 @ X28)
% 0.58/0.80          | ~ (m1_pre_topc @ X28 @ X27)
% 0.58/0.80          | ((u1_struct_0 @ (k2_tsep_1 @ X27 @ X26 @ X28))
% 0.58/0.80              = (k3_xboole_0 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X28)))
% 0.58/0.80          | ~ (m1_pre_topc @ (k2_tsep_1 @ X27 @ X26 @ X28) @ X27)
% 0.58/0.80          | ~ (v1_pre_topc @ (k2_tsep_1 @ X27 @ X26 @ X28))
% 0.58/0.80          | (v2_struct_0 @ (k2_tsep_1 @ X27 @ X26 @ X28))
% 0.58/0.80          | (r1_tsep_1 @ X26 @ X28)
% 0.58/0.80          | ~ (m1_pre_topc @ X26 @ X27)
% 0.58/0.80          | (v2_struct_0 @ X26))),
% 0.58/0.80      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_C_1)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_B)
% 0.58/0.80        | (v2_struct_0 @ sk_B)
% 0.58/0.80        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.58/0.80        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.80        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.80        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.80        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.80            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.80        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_C_1)
% 0.58/0.80        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_A))),
% 0.58/0.80      inference('sup-', [status(thm)], ['21', '23'])).
% 0.58/0.80  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('26', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('28', plain,
% 0.58/0.80      (((v2_struct_0 @ sk_C_1)
% 0.58/0.80        | (v2_struct_0 @ sk_A)
% 0.58/0.80        | (v2_struct_0 @ sk_B)
% 0.58/0.80        | (v2_struct_0 @ sk_B)
% 0.58/0.80        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.80        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.80        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.80        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.80            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.58/0.81  thf('29', plain,
% 0.58/0.81      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('simplify', [status(thm)], ['28'])).
% 0.58/0.81  thf('30', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['20', '29'])).
% 0.58/0.81  thf('31', plain,
% 0.58/0.81      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.81  thf('32', plain,
% 0.58/0.81      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.81         (~ (m1_pre_topc @ X30 @ X31)
% 0.58/0.81          | (v2_struct_0 @ X30)
% 0.58/0.81          | ~ (l1_pre_topc @ X31)
% 0.58/0.81          | (v2_struct_0 @ X31)
% 0.58/0.81          | (v2_struct_0 @ X32)
% 0.58/0.81          | ~ (m1_pre_topc @ X32 @ X31)
% 0.58/0.81          | ~ (v2_struct_0 @ (k2_tsep_1 @ X31 @ X30 @ X32)))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.58/0.81  thf('33', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.58/0.81  thf('34', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('37', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B))),
% 0.58/0.81      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.58/0.81  thf('38', plain,
% 0.58/0.81      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('simplify', [status(thm)], ['37'])).
% 0.58/0.81  thf('39', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_D_1 @ 
% 0.58/0.81        (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(t2_subset, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ A @ B ) =>
% 0.58/0.81       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.58/0.81  thf('40', plain,
% 0.58/0.81      (![X14 : $i, X15 : $i]:
% 0.58/0.81         ((r2_hidden @ X14 @ X15)
% 0.58/0.81          | (v1_xboole_0 @ X15)
% 0.58/0.81          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.58/0.81      inference('cnf', [status(esa)], [t2_subset])).
% 0.58/0.81  thf('41', plain,
% 0.58/0.81      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.58/0.81        | (r2_hidden @ sk_D_1 @ 
% 0.58/0.81           (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.81  thf('42', plain,
% 0.58/0.81      (((r2_hidden @ sk_D_1 @ 
% 0.58/0.81         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.58/0.81      inference('sup+', [status(thm)], ['38', '41'])).
% 0.58/0.81  thf(d3_tarski, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.81  thf('43', plain,
% 0.58/0.81      (![X1 : $i, X3 : $i]:
% 0.58/0.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf(d4_xboole_0, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.58/0.81       ( ![D:$i]:
% 0.58/0.81         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.81           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.58/0.81  thf('44', plain,
% 0.58/0.81      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X8 @ X7)
% 0.58/0.81          | (r2_hidden @ X8 @ X6)
% 0.58/0.81          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.58/0.81      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.58/0.81  thf('45', plain,
% 0.58/0.81      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.58/0.81         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['44'])).
% 0.58/0.81  thf('46', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.81          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['43', '45'])).
% 0.58/0.81  thf('47', plain,
% 0.58/0.81      (![X1 : $i, X3 : $i]:
% 0.58/0.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('48', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.58/0.81          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.81  thf('49', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.58/0.81      inference('simplify', [status(thm)], ['48'])).
% 0.58/0.81  thf(t3_subset, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.81  thf('50', plain,
% 0.58/0.81      (![X16 : $i, X18 : $i]:
% 0.58/0.81         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.58/0.81      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.81  thf('51', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.81  thf(t4_subset, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.58/0.81       ( m1_subset_1 @ A @ C ) ))).
% 0.58/0.81  thf('52', plain,
% 0.58/0.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X19 @ X20)
% 0.58/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.58/0.81          | (m1_subset_1 @ X19 @ X21))),
% 0.58/0.81      inference('cnf', [status(esa)], [t4_subset])).
% 0.58/0.81  thf('53', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((m1_subset_1 @ X2 @ X0)
% 0.58/0.81          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['51', '52'])).
% 0.58/0.81  thf('54', plain,
% 0.58/0.81      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['42', '53'])).
% 0.58/0.81  thf(fc2_struct_0, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.58/0.81       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.81  thf('55', plain,
% 0.58/0.81      (![X25 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.58/0.81          | ~ (l1_struct_0 @ X25)
% 0.58/0.81          | (v2_struct_0 @ X25))),
% 0.58/0.81      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.58/0.81  thf('56', plain,
% 0.58/0.81      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.81  thf('57', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['13', '56'])).
% 0.58/0.81  thf('58', plain,
% 0.58/0.81      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('simplify', [status(thm)], ['57'])).
% 0.58/0.81  thf('59', plain,
% 0.58/0.81      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.81         (~ (m1_pre_topc @ X30 @ X31)
% 0.58/0.81          | (v2_struct_0 @ X30)
% 0.58/0.81          | ~ (l1_pre_topc @ X31)
% 0.58/0.81          | (v2_struct_0 @ X31)
% 0.58/0.81          | (v2_struct_0 @ X32)
% 0.58/0.81          | ~ (m1_pre_topc @ X32 @ X31)
% 0.58/0.81          | ~ (v2_struct_0 @ (k2_tsep_1 @ X31 @ X30 @ X32)))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.58/0.81  thf('60', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 0.58/0.81        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['58', '59'])).
% 0.58/0.81  thf('61', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('63', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('64', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B))),
% 0.58/0.81      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.58/0.81  thf('65', plain,
% 0.58/0.81      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.81  thf('66', plain,
% 0.58/0.81      (![X33 : $i, X34 : $i]:
% 0.58/0.81         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B))
% 0.58/0.81          | ((X33) != (sk_D_1))
% 0.58/0.81          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_C_1))
% 0.58/0.81          | ((X34) != (sk_D_1)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('67', plain,
% 0.58/0.81      ((![X34 : $i]:
% 0.58/0.81          (((X34) != (sk_D_1)) | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_C_1))))
% 0.58/0.81         <= ((![X34 : $i]:
% 0.58/0.81                (((X34) != (sk_D_1))
% 0.58/0.81                 | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_C_1)))))),
% 0.58/0.81      inference('split', [status(esa)], ['66'])).
% 0.58/0.81  thf('68', plain,
% 0.58/0.81      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81         <= ((![X34 : $i]:
% 0.58/0.81                (((X34) != (sk_D_1))
% 0.58/0.81                 | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_C_1)))))),
% 0.58/0.81      inference('simplify', [status(thm)], ['67'])).
% 0.58/0.81  thf('69', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.81  thf('70', plain,
% 0.58/0.81      (((r2_hidden @ sk_D_1 @ 
% 0.58/0.81         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.58/0.81      inference('sup+', [status(thm)], ['38', '41'])).
% 0.58/0.81  thf(t17_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.81  thf('71', plain,
% 0.58/0.81      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.58/0.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.58/0.81  thf('72', plain,
% 0.58/0.81      (![X16 : $i, X18 : $i]:
% 0.58/0.81         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.58/0.81      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.81  thf('73', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['71', '72'])).
% 0.58/0.81  thf('74', plain,
% 0.58/0.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X19 @ X20)
% 0.58/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.58/0.81          | (m1_subset_1 @ X19 @ X21))),
% 0.58/0.81      inference('cnf', [status(esa)], [t4_subset])).
% 0.58/0.81  thf('75', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((m1_subset_1 @ X2 @ X0)
% 0.58/0.81          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['73', '74'])).
% 0.58/0.81  thf('76', plain,
% 0.58/0.81      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['70', '75'])).
% 0.58/0.81  thf('77', plain,
% 0.58/0.81      (![X25 : $i]:
% 0.58/0.81         (~ (v1_xboole_0 @ (u1_struct_0 @ X25))
% 0.58/0.81          | ~ (l1_struct_0 @ X25)
% 0.58/0.81          | (v2_struct_0 @ X25))),
% 0.58/0.81      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.58/0.81  thf('78', plain,
% 0.58/0.81      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['76', '77'])).
% 0.58/0.81  thf('79', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['69', '78'])).
% 0.58/0.81  thf('80', plain,
% 0.58/0.81      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C_1))
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('simplify', [status(thm)], ['79'])).
% 0.58/0.81  thf('81', plain,
% 0.58/0.81      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.81         (~ (m1_pre_topc @ X30 @ X31)
% 0.58/0.81          | (v2_struct_0 @ X30)
% 0.58/0.81          | ~ (l1_pre_topc @ X31)
% 0.58/0.81          | (v2_struct_0 @ X31)
% 0.58/0.81          | (v2_struct_0 @ X32)
% 0.58/0.81          | ~ (m1_pre_topc @ X32 @ X31)
% 0.58/0.81          | ~ (v2_struct_0 @ (k2_tsep_1 @ X31 @ X30 @ X32)))),
% 0.58/0.81      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.58/0.81  thf('82', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.58/0.81        | ~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['80', '81'])).
% 0.58/0.81  thf('83', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('85', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('86', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.58/0.81        | (v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B))),
% 0.58/0.81      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 0.58/0.81  thf('87', plain,
% 0.58/0.81      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('simplify', [status(thm)], ['86'])).
% 0.58/0.81  thf('88', plain,
% 0.58/0.81      ((![X33 : $i]:
% 0.58/0.81          (((X33) != (sk_D_1)) | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B))))
% 0.58/0.81         <= ((![X33 : $i]:
% 0.58/0.81                (((X33) != (sk_D_1))
% 0.58/0.81                 | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.81      inference('split', [status(esa)], ['66'])).
% 0.58/0.81  thf('89', plain,
% 0.58/0.81      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.58/0.81         <= ((![X33 : $i]:
% 0.58/0.81                (((X33) != (sk_D_1))
% 0.58/0.81                 | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.81      inference('simplify', [status(thm)], ['88'])).
% 0.58/0.81  thf('90', plain,
% 0.58/0.81      ((((v2_struct_0 @ sk_C_1)
% 0.58/0.81         | (v2_struct_0 @ sk_A)
% 0.58/0.81         | (v2_struct_0 @ sk_B)
% 0.58/0.81         | (r1_tsep_1 @ sk_B @ sk_C_1)))
% 0.58/0.81         <= ((![X33 : $i]:
% 0.58/0.81                (((X33) != (sk_D_1))
% 0.58/0.81                 | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['87', '89'])).
% 0.58/0.81  thf('91', plain, (~ (r1_tsep_1 @ sk_B @ sk_C_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('92', plain,
% 0.58/0.81      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1)))
% 0.58/0.81         <= ((![X33 : $i]:
% 0.58/0.81                (((X33) != (sk_D_1))
% 0.58/0.81                 | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['90', '91'])).
% 0.58/0.81  thf('93', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('94', plain,
% 0.58/0.81      ((((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A)))
% 0.58/0.81         <= ((![X33 : $i]:
% 0.58/0.81                (((X33) != (sk_D_1))
% 0.58/0.81                 | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.81      inference('clc', [status(thm)], ['92', '93'])).
% 0.58/0.81  thf('95', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('96', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_A))
% 0.58/0.81         <= ((![X33 : $i]:
% 0.58/0.81                (((X33) != (sk_D_1))
% 0.58/0.81                 | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B)))))),
% 0.58/0.81      inference('clc', [status(thm)], ['94', '95'])).
% 0.58/0.81  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('98', plain,
% 0.58/0.81      (~
% 0.58/0.81       (![X33 : $i]:
% 0.58/0.81          (((X33) != (sk_D_1)) | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['96', '97'])).
% 0.58/0.81  thf('99', plain,
% 0.58/0.81      ((![X34 : $i]:
% 0.58/0.81          (((X34) != (sk_D_1)) | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_C_1)))) | 
% 0.58/0.81       (![X33 : $i]:
% 0.58/0.81          (((X33) != (sk_D_1)) | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B))))),
% 0.58/0.81      inference('split', [status(esa)], ['66'])).
% 0.58/0.81  thf('100', plain,
% 0.58/0.81      ((![X34 : $i]:
% 0.58/0.81          (((X34) != (sk_D_1)) | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ sk_C_1))))),
% 0.58/0.81      inference('sat_resolution*', [status(thm)], ['98', '99'])).
% 0.58/0.81  thf('101', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('simpl_trail', [status(thm)], ['68', '100'])).
% 0.58/0.81  thf('102', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_C_1)
% 0.58/0.81        | (v2_struct_0 @ sk_A)
% 0.58/0.81        | (v2_struct_0 @ sk_B)
% 0.58/0.81        | (r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['65', '101'])).
% 0.58/0.81  thf('103', plain, (~ (r1_tsep_1 @ sk_B @ sk_C_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('104', plain,
% 0.58/0.81      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C_1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['102', '103'])).
% 0.58/0.81  thf('105', plain, (~ (v2_struct_0 @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('106', plain, (((v2_struct_0 @ sk_C_1) | (v2_struct_0 @ sk_A))),
% 0.58/0.81      inference('clc', [status(thm)], ['104', '105'])).
% 0.58/0.81  thf('107', plain, (~ (v2_struct_0 @ sk_C_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('108', plain, ((v2_struct_0 @ sk_A)),
% 0.58/0.81      inference('clc', [status(thm)], ['106', '107'])).
% 0.58/0.81  thf('109', plain, ($false), inference('demod', [status(thm)], ['0', '108'])).
% 0.58/0.81  
% 0.58/0.81  % SZS output end Refutation
% 0.58/0.81  
% 0.63/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
