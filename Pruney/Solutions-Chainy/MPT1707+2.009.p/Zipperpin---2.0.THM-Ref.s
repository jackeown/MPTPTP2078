%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ggAJQ8BEW7

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:12 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 157 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   28
%              Number of atoms          : 1065 (3027 expanded)
%              Number of equality atoms :   21 ( 117 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) @ X19 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( X16
       != ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
      | ( ( u1_struct_0 @ X16 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) @ X15 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X15 @ X14 @ X17 ) )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

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
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('44',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
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
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X21: $i] :
      ( ( X21 != sk_D_1 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
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
    ! [X22: $i] :
      ( ( X22 != sk_D_1 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_B ) ) ) ),
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
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ggAJQ8BEW7
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 312 iterations in 0.264s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.71  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.71  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.52/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.52/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.71  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.71  thf(t16_tmap_1, conjecture,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.52/0.71           ( ![C:$i]:
% 0.52/0.71             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.52/0.71               ( ![D:$i]:
% 0.52/0.71                 ( ( m1_subset_1 @
% 0.52/0.71                     D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.52/0.71                   ( ~( ( ![E:$i]:
% 0.52/0.71                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.52/0.71                            ( ( E ) != ( D ) ) ) ) & 
% 0.52/0.71                        ( ![E:$i]:
% 0.52/0.71                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.52/0.71                            ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i]:
% 0.52/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.52/0.71            ( l1_pre_topc @ A ) ) =>
% 0.52/0.71          ( ![B:$i]:
% 0.52/0.71            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.52/0.71              ( ![C:$i]:
% 0.52/0.71                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.52/0.71                  ( ![D:$i]:
% 0.52/0.71                    ( ( m1_subset_1 @
% 0.52/0.71                        D @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) =>
% 0.52/0.71                      ( ~( ( ![E:$i]:
% 0.52/0.71                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.52/0.71                               ( ( E ) != ( D ) ) ) ) & 
% 0.52/0.71                           ( ![E:$i]:
% 0.52/0.71                             ( ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) =>
% 0.52/0.71                               ( ( E ) != ( D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t16_tmap_1])).
% 0.52/0.71  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(dt_k1_tsep_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.52/0.71         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.52/0.71         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.52/0.71       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 0.52/0.71         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 0.52/0.71         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.71         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.71          | (v2_struct_0 @ X18)
% 0.52/0.71          | ~ (l1_pre_topc @ X19)
% 0.52/0.71          | (v2_struct_0 @ X19)
% 0.52/0.71          | (v2_struct_0 @ X20)
% 0.52/0.71          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.71          | (m1_pre_topc @ (k1_tsep_1 @ X19 @ X18 @ X20) @ X19))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.52/0.71          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ X0)
% 0.52/0.71          | (v2_struct_0 @ sk_A)
% 0.52/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.52/0.71          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ X0)
% 0.52/0.71          | (v2_struct_0 @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['1', '6'])).
% 0.52/0.71  thf(dt_m1_pre_topc, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      (![X11 : $i, X12 : $i]:
% 0.52/0.71         (~ (m1_pre_topc @ X11 @ X12)
% 0.52/0.71          | (l1_pre_topc @ X11)
% 0.52/0.71          | ~ (l1_pre_topc @ X12))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.71  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.71      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.71  thf(dt_l1_pre_topc, axiom,
% 0.52/0.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.71         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.71          | (v2_struct_0 @ X18)
% 0.52/0.71          | ~ (l1_pre_topc @ X19)
% 0.52/0.71          | (v2_struct_0 @ X19)
% 0.52/0.71          | (v2_struct_0 @ X20)
% 0.52/0.71          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.71          | (v1_pre_topc @ (k1_tsep_1 @ X19 @ X18 @ X20)))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 0.52/0.71          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ X0)
% 0.52/0.71          | (v2_struct_0 @ sk_A)
% 0.52/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.71  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 0.52/0.71          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ X0)
% 0.52/0.71          | (v2_struct_0 @ sk_A)
% 0.52/0.71          | (v2_struct_0 @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['14', '19'])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['1', '6'])).
% 0.52/0.71  thf(d2_tsep_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.52/0.71           ( ![C:$i]:
% 0.52/0.71             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.52/0.71               ( ![D:$i]:
% 0.52/0.71                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.52/0.71                     ( m1_pre_topc @ D @ A ) ) =>
% 0.52/0.71                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.52/0.71                     ( ( u1_struct_0 @ D ) =
% 0.52/0.71                       ( k2_xboole_0 @
% 0.52/0.71                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.71         ((v2_struct_0 @ X14)
% 0.52/0.71          | ~ (m1_pre_topc @ X14 @ X15)
% 0.52/0.71          | (v2_struct_0 @ X16)
% 0.52/0.71          | ~ (v1_pre_topc @ X16)
% 0.52/0.71          | ~ (m1_pre_topc @ X16 @ X15)
% 0.52/0.71          | ((X16) != (k1_tsep_1 @ X15 @ X14 @ X17))
% 0.52/0.71          | ((u1_struct_0 @ X16)
% 0.52/0.71              = (k2_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17)))
% 0.52/0.71          | ~ (m1_pre_topc @ X17 @ X15)
% 0.52/0.71          | (v2_struct_0 @ X17)
% 0.52/0.71          | ~ (l1_pre_topc @ X15)
% 0.52/0.71          | (v2_struct_0 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.52/0.71         ((v2_struct_0 @ X15)
% 0.52/0.71          | ~ (l1_pre_topc @ X15)
% 0.52/0.71          | (v2_struct_0 @ X17)
% 0.52/0.71          | ~ (m1_pre_topc @ X17 @ X15)
% 0.52/0.71          | ((u1_struct_0 @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 0.52/0.71              = (k2_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X17)))
% 0.52/0.71          | ~ (m1_pre_topc @ (k1_tsep_1 @ X15 @ X14 @ X17) @ X15)
% 0.52/0.71          | ~ (v1_pre_topc @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 0.52/0.71          | (v2_struct_0 @ (k1_tsep_1 @ X15 @ X14 @ X17))
% 0.52/0.71          | ~ (m1_pre_topc @ X14 @ X15)
% 0.52/0.71          | (v2_struct_0 @ X14))),
% 0.52/0.71      inference('simplify', [status(thm)], ['22'])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.71        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['21', '23'])).
% 0.52/0.71  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.71        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C))),
% 0.52/0.71      inference('simplify', [status(thm)], ['28'])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['20', '29'])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C))),
% 0.52/0.71      inference('simplify', [status(thm)], ['30'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.71         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.71          | (v2_struct_0 @ X18)
% 0.52/0.71          | ~ (l1_pre_topc @ X19)
% 0.52/0.71          | (v2_struct_0 @ X19)
% 0.52/0.71          | (v2_struct_0 @ X20)
% 0.52/0.71          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.71          | ~ (v2_struct_0 @ (k1_tsep_1 @ X19 @ X18 @ X20)))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.71        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.71  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C))),
% 0.52/0.71      inference('simplify', [status(thm)], ['37'])).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t2_subset, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ A @ B ) =>
% 0.52/0.71       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      (![X8 : $i, X9 : $i]:
% 0.52/0.71         ((r2_hidden @ X8 @ X9)
% 0.52/0.71          | (v1_xboole_0 @ X9)
% 0.52/0.71          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.52/0.71      inference('cnf', [status(esa)], [t2_subset])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ 
% 0.52/0.71           (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.71  thf('42', plain,
% 0.52/0.71      (((r2_hidden @ sk_D_1 @ 
% 0.52/0.71         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['38', '41'])).
% 0.52/0.71  thf(d3_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.52/0.71       ( ![D:$i]:
% 0.52/0.71         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.71           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.71          | (r2_hidden @ X4 @ X3)
% 0.52/0.71          | (r2_hidden @ X4 @ X1)
% 0.52/0.71          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.52/0.71         ((r2_hidden @ X4 @ X1)
% 0.52/0.71          | (r2_hidden @ X4 @ X3)
% 0.52/0.71          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['43'])).
% 0.52/0.71  thf('45', plain,
% 0.52/0.71      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['42', '44'])).
% 0.52/0.71  thf(fc2_struct_0, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.52/0.71       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.71  thf('46', plain,
% 0.52/0.71      (![X13 : $i]:
% 0.52/0.71         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.52/0.71          | ~ (l1_struct_0 @ X13)
% 0.52/0.71          | (v2_struct_0 @ X13))),
% 0.52/0.71      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.52/0.71  thf('47', plain,
% 0.52/0.71      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['13', '47'])).
% 0.52/0.71  thf('49', plain,
% 0.52/0.71      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C))),
% 0.52/0.71      inference('simplify', [status(thm)], ['48'])).
% 0.52/0.71  thf('50', plain,
% 0.52/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.71         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.71          | (v2_struct_0 @ X18)
% 0.52/0.71          | ~ (l1_pre_topc @ X19)
% 0.52/0.71          | (v2_struct_0 @ X19)
% 0.52/0.71          | (v2_struct_0 @ X20)
% 0.52/0.71          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.71          | ~ (v2_struct_0 @ (k1_tsep_1 @ X19 @ X18 @ X20)))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 0.52/0.71  thf('51', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.71        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['49', '50'])).
% 0.52/0.71  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('54', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('55', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.52/0.71  thf('56', plain,
% 0.52/0.71      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C))),
% 0.52/0.71      inference('simplify', [status(thm)], ['55'])).
% 0.52/0.71  thf(t1_subset, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.52/0.71      inference('cnf', [status(esa)], [t1_subset])).
% 0.52/0.71  thf('58', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.71  thf('59', plain,
% 0.52/0.71      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.52/0.71      inference('cnf', [status(esa)], [t1_subset])).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.71        | (v2_struct_0 @ sk_B)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      (![X21 : $i]:
% 0.52/0.71         (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('62', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C))),
% 0.52/0.71      inference('simplify', [status(thm)], ['61'])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.71        | (v2_struct_0 @ sk_C)
% 0.52/0.71        | (v2_struct_0 @ sk_A)
% 0.52/0.71        | (v2_struct_0 @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['60', '62'])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X22 : $i]:
% 0.52/0.71         (((X22) != (sk_D_1)) | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('65', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 0.52/0.71      inference('simplify', [status(thm)], ['64'])).
% 0.52/0.71  thf('66', plain,
% 0.52/0.71      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.52/0.71      inference('sup-', [status(thm)], ['63', '65'])).
% 0.52/0.71  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('68', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.52/0.71      inference('clc', [status(thm)], ['66', '67'])).
% 0.52/0.71  thf('69', plain, (~ (v2_struct_0 @ sk_C)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('70', plain, ((v2_struct_0 @ sk_A)),
% 0.52/0.71      inference('clc', [status(thm)], ['68', '69'])).
% 0.52/0.71  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
