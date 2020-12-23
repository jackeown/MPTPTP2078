%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EnU1UCccTC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:11 EST 2020

% Result     : Theorem 1.99s
% Output     : Refutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 157 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   28
%              Number of atoms          : 1072 (3034 expanded)
%              Number of equality atoms :   21 ( 117 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t16_tmap_1,conjecture,(
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
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                 => ~ ( ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                         => ( E != D ) )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) )
                         => ( E != D ) ) ) ) ) ) ) )).

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
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) )
                   => ~ ( ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                           => ( E != D ) )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) )
                           => ( E != D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X27 @ X26 @ X28 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
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
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
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
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( v1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( X24
       != ( k1_tsep_1 @ X23 @ X22 @ X25 ) )
      | ( ( u1_struct_0 @ X24 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('23',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X23 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X23 @ X22 @ X25 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X23 @ X22 @ X25 ) @ X23 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X23 @ X22 @ X25 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X23 @ X22 @ X25 ) )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('44',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X27 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X32: $i] :
      ( ( X32 != sk_D_1 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X33: $i] :
      ( ( X33 != sk_D_1 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EnU1UCccTC
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:44:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.99/2.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.99/2.23  % Solved by: fo/fo7.sh
% 1.99/2.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.99/2.23  % done 2571 iterations in 1.733s
% 1.99/2.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.99/2.23  % SZS output start Refutation
% 1.99/2.23  thf(sk_A_type, type, sk_A: $i).
% 1.99/2.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.99/2.23  thf(sk_B_type, type, sk_B: $i).
% 1.99/2.23  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.99/2.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.99/2.23  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.99/2.23  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.99/2.23  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.99/2.23  thf(sk_C_type, type, sk_C: $i).
% 1.99/2.23  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.99/2.23  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.99/2.23  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.99/2.23  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.99/2.23  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.99/2.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.99/2.23  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.99/2.23  thf(t16_tmap_1, conjecture,
% 1.99/2.23    (![A:$i]:
% 1.99/2.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.99/2.23       ( ![B:$i]:
% 1.99/2.23         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.99/2.23           ( ![C:$i]:
% 1.99/2.23             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.99/2.23               ( ![D:$i]:
% 1.99/2.23                 ( ( m1_subset_1 @
% 1.99/2.23                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 1.99/2.23                   ( ~( ( ![E:$i]:
% 1.99/2.23                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.99/2.23                            ( ( E ) != ( D ) ) ) ) & 
% 1.99/2.23                        ( ![E:$i]:
% 1.99/2.23                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 1.99/2.23                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.99/2.23  thf(zf_stmt_0, negated_conjecture,
% 1.99/2.23    (~( ![A:$i]:
% 1.99/2.23        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.99/2.23            ( l1_pre_topc @ A ) ) =>
% 1.99/2.23          ( ![B:$i]:
% 1.99/2.23            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.99/2.23              ( ![C:$i]:
% 1.99/2.23                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.99/2.23                  ( ![D:$i]:
% 1.99/2.23                    ( ( m1_subset_1 @
% 1.99/2.23                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 1.99/2.23                      ( ~( ( ![E:$i]:
% 1.99/2.23                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.99/2.23                               ( ( E ) != ( D ) ) ) ) & 
% 1.99/2.23                           ( ![E:$i]:
% 1.99/2.23                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 1.99/2.23                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.99/2.23    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 1.99/2.23  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf(dt_k1_tsep_1, axiom,
% 1.99/2.23    (![A:$i,B:$i,C:$i]:
% 1.99/2.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.99/2.23         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.99/2.23         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.99/2.23       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.99/2.23         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.99/2.23         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.99/2.23  thf('3', plain,
% 1.99/2.23      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.99/2.23         (~ (m1_pre_topc @ X26 @ X27)
% 1.99/2.23          | (v2_struct_0 @ X26)
% 1.99/2.23          | ~ (l1_pre_topc @ X27)
% 1.99/2.23          | (v2_struct_0 @ X27)
% 1.99/2.23          | (v2_struct_0 @ X28)
% 1.99/2.23          | ~ (m1_pre_topc @ X28 @ X27)
% 1.99/2.23          | (m1_pre_topc @ (k1_tsep_1 @ X27 @ X26 @ X28) @ X27))),
% 1.99/2.23      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.99/2.23  thf('4', plain,
% 1.99/2.23      (![X0 : $i]:
% 1.99/2.23         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.99/2.23          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.99/2.23          | (v2_struct_0 @ X0)
% 1.99/2.23          | (v2_struct_0 @ sk_A)
% 1.99/2.23          | ~ (l1_pre_topc @ sk_A)
% 1.99/2.23          | (v2_struct_0 @ sk_B))),
% 1.99/2.23      inference('sup-', [status(thm)], ['2', '3'])).
% 1.99/2.23  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('6', plain,
% 1.99/2.23      (![X0 : $i]:
% 1.99/2.23         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.99/2.23          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.99/2.23          | (v2_struct_0 @ X0)
% 1.99/2.23          | (v2_struct_0 @ sk_A)
% 1.99/2.23          | (v2_struct_0 @ sk_B))),
% 1.99/2.23      inference('demod', [status(thm)], ['4', '5'])).
% 1.99/2.23  thf('7', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.99/2.23      inference('sup-', [status(thm)], ['1', '6'])).
% 1.99/2.23  thf(dt_m1_pre_topc, axiom,
% 1.99/2.23    (![A:$i]:
% 1.99/2.23     ( ( l1_pre_topc @ A ) =>
% 1.99/2.23       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.99/2.23  thf('8', plain,
% 1.99/2.23      (![X16 : $i, X17 : $i]:
% 1.99/2.23         (~ (m1_pre_topc @ X16 @ X17)
% 1.99/2.23          | (l1_pre_topc @ X16)
% 1.99/2.23          | ~ (l1_pre_topc @ X17))),
% 1.99/2.23      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.99/2.23  thf('9', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | ~ (l1_pre_topc @ sk_A)
% 1.99/2.23        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.99/2.23      inference('sup-', [status(thm)], ['7', '8'])).
% 1.99/2.23  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('11', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.99/2.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.99/2.23  thf(dt_l1_pre_topc, axiom,
% 1.99/2.23    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.99/2.23  thf('12', plain,
% 1.99/2.23      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 1.99/2.23      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.99/2.23  thf('13', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.99/2.23      inference('sup-', [status(thm)], ['11', '12'])).
% 1.99/2.23  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('16', plain,
% 1.99/2.23      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.99/2.23         (~ (m1_pre_topc @ X26 @ X27)
% 1.99/2.23          | (v2_struct_0 @ X26)
% 1.99/2.23          | ~ (l1_pre_topc @ X27)
% 1.99/2.23          | (v2_struct_0 @ X27)
% 1.99/2.23          | (v2_struct_0 @ X28)
% 1.99/2.23          | ~ (m1_pre_topc @ X28 @ X27)
% 1.99/2.23          | (v1_pre_topc @ (k1_tsep_1 @ X27 @ X26 @ X28)))),
% 1.99/2.23      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.99/2.23  thf('17', plain,
% 1.99/2.23      (![X0 : $i]:
% 1.99/2.23         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.99/2.23          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.99/2.23          | (v2_struct_0 @ X0)
% 1.99/2.23          | (v2_struct_0 @ sk_A)
% 1.99/2.23          | ~ (l1_pre_topc @ sk_A)
% 1.99/2.23          | (v2_struct_0 @ sk_B))),
% 1.99/2.23      inference('sup-', [status(thm)], ['15', '16'])).
% 1.99/2.23  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('19', plain,
% 1.99/2.23      (![X0 : $i]:
% 1.99/2.23         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.99/2.23          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.99/2.23          | (v2_struct_0 @ X0)
% 1.99/2.23          | (v2_struct_0 @ sk_A)
% 1.99/2.23          | (v2_struct_0 @ sk_B))),
% 1.99/2.23      inference('demod', [status(thm)], ['17', '18'])).
% 1.99/2.23  thf('20', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.99/2.23      inference('sup-', [status(thm)], ['14', '19'])).
% 1.99/2.23  thf('21', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.99/2.23      inference('sup-', [status(thm)], ['1', '6'])).
% 1.99/2.23  thf(d2_tsep_1, axiom,
% 1.99/2.23    (![A:$i]:
% 1.99/2.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.99/2.23       ( ![B:$i]:
% 1.99/2.23         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.99/2.23           ( ![C:$i]:
% 1.99/2.23             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.99/2.23               ( ![D:$i]:
% 1.99/2.23                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.99/2.23                     ( m1_pre_topc @ D @ A ) ) =>
% 1.99/2.23                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.99/2.23                     ( ( u1_struct_0 @ D ) =
% 1.99/2.23                       ( k2_xboole_0 @
% 1.99/2.23                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.99/2.23  thf('22', plain,
% 1.99/2.23      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.99/2.23         ((v2_struct_0 @ X22)
% 1.99/2.23          | ~ (m1_pre_topc @ X22 @ X23)
% 1.99/2.23          | (v2_struct_0 @ X24)
% 1.99/2.23          | ~ (v1_pre_topc @ X24)
% 1.99/2.23          | ~ (m1_pre_topc @ X24 @ X23)
% 1.99/2.23          | ((X24) != (k1_tsep_1 @ X23 @ X22 @ X25))
% 1.99/2.23          | ((u1_struct_0 @ X24)
% 1.99/2.23              = (k2_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25)))
% 1.99/2.23          | ~ (m1_pre_topc @ X25 @ X23)
% 1.99/2.23          | (v2_struct_0 @ X25)
% 1.99/2.23          | ~ (l1_pre_topc @ X23)
% 1.99/2.23          | (v2_struct_0 @ X23))),
% 1.99/2.23      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.99/2.23  thf('23', plain,
% 1.99/2.23      (![X22 : $i, X23 : $i, X25 : $i]:
% 1.99/2.23         ((v2_struct_0 @ X23)
% 1.99/2.23          | ~ (l1_pre_topc @ X23)
% 1.99/2.23          | (v2_struct_0 @ X25)
% 1.99/2.23          | ~ (m1_pre_topc @ X25 @ X23)
% 1.99/2.23          | ((u1_struct_0 @ (k1_tsep_1 @ X23 @ X22 @ X25))
% 1.99/2.23              = (k2_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X25)))
% 1.99/2.23          | ~ (m1_pre_topc @ (k1_tsep_1 @ X23 @ X22 @ X25) @ X23)
% 1.99/2.23          | ~ (v1_pre_topc @ (k1_tsep_1 @ X23 @ X22 @ X25))
% 1.99/2.23          | (v2_struct_0 @ (k1_tsep_1 @ X23 @ X22 @ X25))
% 1.99/2.23          | ~ (m1_pre_topc @ X22 @ X23)
% 1.99/2.23          | (v2_struct_0 @ X22))),
% 1.99/2.23      inference('simplify', [status(thm)], ['22'])).
% 1.99/2.23  thf('24', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.99/2.23        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | ~ (l1_pre_topc @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_A))),
% 1.99/2.23      inference('sup-', [status(thm)], ['21', '23'])).
% 1.99/2.23  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('28', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A))),
% 1.99/2.23      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 1.99/2.23  thf('29', plain,
% 1.99/2.23      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.99/2.23        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C))),
% 1.99/2.23      inference('simplify', [status(thm)], ['28'])).
% 1.99/2.23  thf('30', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.99/2.23      inference('sup-', [status(thm)], ['20', '29'])).
% 1.99/2.23  thf('31', plain,
% 1.99/2.23      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.99/2.23        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C))),
% 1.99/2.23      inference('simplify', [status(thm)], ['30'])).
% 1.99/2.23  thf('32', plain,
% 1.99/2.23      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.99/2.23         (~ (m1_pre_topc @ X26 @ X27)
% 1.99/2.23          | (v2_struct_0 @ X26)
% 1.99/2.23          | ~ (l1_pre_topc @ X27)
% 1.99/2.23          | (v2_struct_0 @ X27)
% 1.99/2.23          | (v2_struct_0 @ X28)
% 1.99/2.23          | ~ (m1_pre_topc @ X28 @ X27)
% 1.99/2.23          | ~ (v2_struct_0 @ (k1_tsep_1 @ X27 @ X26 @ X28)))),
% 1.99/2.23      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.99/2.23  thf('33', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.99/2.23        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | ~ (l1_pre_topc @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.99/2.23      inference('sup-', [status(thm)], ['31', '32'])).
% 1.99/2.23  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('37', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B))),
% 1.99/2.23      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 1.99/2.23  thf('38', plain,
% 1.99/2.23      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C))),
% 1.99/2.23      inference('simplify', [status(thm)], ['37'])).
% 1.99/2.23  thf('39', plain,
% 1.99/2.23      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf(d2_subset_1, axiom,
% 1.99/2.23    (![A:$i,B:$i]:
% 1.99/2.23     ( ( ( v1_xboole_0 @ A ) =>
% 1.99/2.23         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.99/2.23       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.99/2.23         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.99/2.23  thf('40', plain,
% 1.99/2.23      (![X10 : $i, X11 : $i]:
% 1.99/2.23         (~ (m1_subset_1 @ X10 @ X11)
% 1.99/2.23          | (r2_hidden @ X10 @ X11)
% 1.99/2.23          | (v1_xboole_0 @ X11))),
% 1.99/2.23      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.99/2.23  thf('41', plain,
% 1.99/2.23      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ 
% 1.99/2.23           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.99/2.23      inference('sup-', [status(thm)], ['39', '40'])).
% 1.99/2.23  thf('42', plain,
% 1.99/2.23      (((r2_hidden @ sk_D_1 @ 
% 1.99/2.23         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.99/2.23      inference('sup+', [status(thm)], ['38', '41'])).
% 1.99/2.23  thf(d3_xboole_0, axiom,
% 1.99/2.23    (![A:$i,B:$i,C:$i]:
% 1.99/2.23     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.99/2.23       ( ![D:$i]:
% 1.99/2.23         ( ( r2_hidden @ D @ C ) <=>
% 1.99/2.23           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.99/2.23  thf('43', plain,
% 1.99/2.23      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.99/2.23         (~ (r2_hidden @ X6 @ X4)
% 1.99/2.23          | (r2_hidden @ X6 @ X5)
% 1.99/2.23          | (r2_hidden @ X6 @ X3)
% 1.99/2.23          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.99/2.23      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.99/2.23  thf('44', plain,
% 1.99/2.23      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.99/2.23         ((r2_hidden @ X6 @ X3)
% 1.99/2.23          | (r2_hidden @ X6 @ X5)
% 1.99/2.23          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 1.99/2.23      inference('simplify', [status(thm)], ['43'])).
% 1.99/2.23  thf('45', plain,
% 1.99/2.23      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.99/2.23      inference('sup-', [status(thm)], ['42', '44'])).
% 1.99/2.23  thf(fc2_struct_0, axiom,
% 1.99/2.23    (![A:$i]:
% 1.99/2.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.99/2.23       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.99/2.23  thf('46', plain,
% 1.99/2.23      (![X18 : $i]:
% 1.99/2.23         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 1.99/2.23          | ~ (l1_struct_0 @ X18)
% 1.99/2.23          | (v2_struct_0 @ X18))),
% 1.99/2.23      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.99/2.23  thf('47', plain,
% 1.99/2.23      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.99/2.23      inference('sup-', [status(thm)], ['45', '46'])).
% 1.99/2.23  thf('48', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.99/2.23      inference('sup-', [status(thm)], ['13', '47'])).
% 1.99/2.23  thf('49', plain,
% 1.99/2.23      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C))),
% 1.99/2.23      inference('simplify', [status(thm)], ['48'])).
% 1.99/2.23  thf('50', plain,
% 1.99/2.23      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.99/2.23         (~ (m1_pre_topc @ X26 @ X27)
% 1.99/2.23          | (v2_struct_0 @ X26)
% 1.99/2.23          | ~ (l1_pre_topc @ X27)
% 1.99/2.23          | (v2_struct_0 @ X27)
% 1.99/2.23          | (v2_struct_0 @ X28)
% 1.99/2.23          | ~ (m1_pre_topc @ X28 @ X27)
% 1.99/2.23          | ~ (v2_struct_0 @ (k1_tsep_1 @ X27 @ X26 @ X28)))),
% 1.99/2.23      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.99/2.23  thf('51', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.99/2.23        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | ~ (l1_pre_topc @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.99/2.23      inference('sup-', [status(thm)], ['49', '50'])).
% 1.99/2.23  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('54', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('55', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B))),
% 1.99/2.23      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 1.99/2.23  thf('56', plain,
% 1.99/2.23      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C))),
% 1.99/2.23      inference('simplify', [status(thm)], ['55'])).
% 1.99/2.23  thf(t1_subset, axiom,
% 1.99/2.23    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.99/2.23  thf('57', plain,
% 1.99/2.23      (![X13 : $i, X14 : $i]:
% 1.99/2.23         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 1.99/2.23      inference('cnf', [status(esa)], [t1_subset])).
% 1.99/2.23  thf('58', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 1.99/2.23      inference('sup-', [status(thm)], ['56', '57'])).
% 1.99/2.23  thf('59', plain,
% 1.99/2.23      (![X13 : $i, X14 : $i]:
% 1.99/2.23         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 1.99/2.23      inference('cnf', [status(esa)], [t1_subset])).
% 1.99/2.23  thf('60', plain,
% 1.99/2.23      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 1.99/2.23        | (v2_struct_0 @ sk_B)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 1.99/2.23      inference('sup-', [status(thm)], ['58', '59'])).
% 1.99/2.23  thf('61', plain,
% 1.99/2.23      (![X32 : $i]:
% 1.99/2.23         (((X32) != (sk_D_1)) | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ sk_C)))),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('62', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 1.99/2.23      inference('simplify', [status(thm)], ['61'])).
% 1.99/2.23  thf('63', plain,
% 1.99/2.23      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 1.99/2.23        | (v2_struct_0 @ sk_C)
% 1.99/2.23        | (v2_struct_0 @ sk_A)
% 1.99/2.23        | (v2_struct_0 @ sk_B))),
% 1.99/2.23      inference('sup-', [status(thm)], ['60', '62'])).
% 1.99/2.23  thf('64', plain,
% 1.99/2.23      (![X33 : $i]:
% 1.99/2.23         (((X33) != (sk_D_1)) | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ sk_B)))),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('65', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 1.99/2.23      inference('simplify', [status(thm)], ['64'])).
% 1.99/2.23  thf('66', plain,
% 1.99/2.23      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.99/2.23      inference('sup-', [status(thm)], ['63', '65'])).
% 1.99/2.23  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('68', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.99/2.23      inference('clc', [status(thm)], ['66', '67'])).
% 1.99/2.23  thf('69', plain, (~ (v2_struct_0 @ sk_C)),
% 1.99/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.99/2.23  thf('70', plain, ((v2_struct_0 @ sk_A)),
% 1.99/2.23      inference('clc', [status(thm)], ['68', '69'])).
% 1.99/2.23  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 1.99/2.23  
% 1.99/2.23  % SZS output end Refutation
% 1.99/2.23  
% 1.99/2.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
