%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R4bIsVoBrg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:13 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  194 ( 833 expanded)
%              Number of leaves         :   25 ( 232 expanded)
%              Depth                    :   38
%              Number of atoms          : 2085 (18706 expanded)
%              Number of equality atoms :   62 ( 759 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    m1_pre_topc @ sk_C @ sk_A ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X18 @ X17 @ X19 ) @ X18 ) ) ),
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
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X18 @ X17 @ X19 ) ) ) ),
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
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( r1_tsep_1 @ X13 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( v1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( X16
       != ( k2_tsep_1 @ X14 @ X13 @ X15 ) )
      | ( ( u1_struct_0 @ X16 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X14 @ X13 @ X15 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X14 @ X13 @ X15 ) @ X14 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X14 @ X13 @ X15 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X14 @ X13 @ X15 ) )
      | ( r1_tsep_1 @ X13 @ X15 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
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
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
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
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
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
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('43',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
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
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) )
      | ( X20 != sk_D_1 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) )
      | ( X21 != sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('63',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('65',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('68',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X18 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('81',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( m1_subset_1 @ X8 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('87',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('89',plain,(
    m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('96',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('107',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['100','107'])).

thf('109',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['87','115'])).

thf('117',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['84','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ~ ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) )
    | ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('125',plain,(
    ! [X20: $i] :
      ( ( X20 != sk_D_1 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['61','125'])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','126'])).

thf('128',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ( m1_subset_1 @ X8 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('131',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('132',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('134',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('135',plain,
    ( ( r2_hidden @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( m1_subset_1 @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('137',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('139',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('146',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('150',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['143','150'])).

thf('152',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ sk_D_1 ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ sk_D_1 )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 != sk_D_1 )
        | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','158'])).

thf('160',plain,(
    ! [X20: $i] :
      ( ( X20 != sk_D_1 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['123','124'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','161'])).

thf('163',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    $false ),
    inference(demod,[status(thm)],['0','166'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R4bIsVoBrg
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:01:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 408 iterations in 0.292s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.78  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.59/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.78  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.59/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.78  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.59/0.78  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.59/0.78  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.78  thf(t17_tmap_1, conjecture,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.78           ( ![C:$i]:
% 0.59/0.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.78               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.59/0.78                 ( ![D:$i]:
% 0.59/0.78                   ( ( m1_subset_1 @
% 0.59/0.78                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.59/0.78                     ( ( ?[E:$i]:
% 0.59/0.78                         ( ( ( E ) = ( D ) ) & 
% 0.59/0.78                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.59/0.78                       ( ?[E:$i]:
% 0.59/0.78                         ( ( ( E ) = ( D ) ) & 
% 0.59/0.78                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i]:
% 0.59/0.78        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.78            ( l1_pre_topc @ A ) ) =>
% 0.59/0.78          ( ![B:$i]:
% 0.59/0.78            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.78              ( ![C:$i]:
% 0.59/0.78                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.78                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.59/0.78                    ( ![D:$i]:
% 0.59/0.78                      ( ( m1_subset_1 @
% 0.59/0.78                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.59/0.78                        ( ( ?[E:$i]:
% 0.59/0.78                            ( ( ( E ) = ( D ) ) & 
% 0.59/0.78                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.59/0.78                          ( ?[E:$i]:
% 0.59/0.78                            ( ( ( E ) = ( D ) ) & 
% 0.59/0.78                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 0.59/0.78  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(dt_k2_tsep_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.59/0.78         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.59/0.78         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.78       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 0.59/0.78         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 0.59/0.78         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (l1_pre_topc @ X18)
% 0.59/0.78          | (v2_struct_0 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X19)
% 0.59/0.78          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.78          | (m1_pre_topc @ (k2_tsep_1 @ X18 @ X17 @ X19) @ X18))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.59/0.78          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ X0)
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.78  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('6', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.59/0.78          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ X0)
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['4', '5'])).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '6'])).
% 0.59/0.78  thf(dt_m1_pre_topc, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( l1_pre_topc @ A ) =>
% 0.59/0.78       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.59/0.78  thf('8', plain,
% 0.59/0.78      (![X10 : $i, X11 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X10 @ X11)
% 0.59/0.78          | (l1_pre_topc @ X10)
% 0.59/0.78          | ~ (l1_pre_topc @ X11))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.78  thf('9', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.78        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.78  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.78  thf(dt_l1_pre_topc, axiom,
% 0.59/0.78    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.78  thf('12', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.78  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (l1_pre_topc @ X18)
% 0.59/0.78          | (v2_struct_0 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X19)
% 0.59/0.78          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.78          | (v1_pre_topc @ (k2_tsep_1 @ X18 @ X17 @ X19)))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.59/0.78          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ X0)
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.78  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('19', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.59/0.78          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ X0)
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['14', '19'])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '6'])).
% 0.59/0.78  thf(d5_tsep_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.59/0.78           ( ![C:$i]:
% 0.59/0.78             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.78               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.59/0.78                 ( ![D:$i]:
% 0.59/0.78                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.59/0.78                       ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.78                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 0.59/0.78                       ( ( u1_struct_0 @ D ) =
% 0.59/0.78                         ( k3_xboole_0 @
% 0.59/0.78                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.78         ((v2_struct_0 @ X13)
% 0.59/0.78          | ~ (m1_pre_topc @ X13 @ X14)
% 0.59/0.78          | (r1_tsep_1 @ X13 @ X15)
% 0.59/0.78          | (v2_struct_0 @ X16)
% 0.59/0.78          | ~ (v1_pre_topc @ X16)
% 0.59/0.78          | ~ (m1_pre_topc @ X16 @ X14)
% 0.59/0.78          | ((X16) != (k2_tsep_1 @ X14 @ X13 @ X15))
% 0.59/0.78          | ((u1_struct_0 @ X16)
% 0.59/0.78              = (k3_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15)))
% 0.59/0.78          | ~ (m1_pre_topc @ X15 @ X14)
% 0.59/0.78          | (v2_struct_0 @ X15)
% 0.59/0.78          | ~ (l1_pre_topc @ X14)
% 0.59/0.78          | (v2_struct_0 @ X14))),
% 0.59/0.78      inference('cnf', [status(esa)], [d5_tsep_1])).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.78         ((v2_struct_0 @ X14)
% 0.59/0.78          | ~ (l1_pre_topc @ X14)
% 0.59/0.78          | (v2_struct_0 @ X15)
% 0.59/0.78          | ~ (m1_pre_topc @ X15 @ X14)
% 0.59/0.78          | ((u1_struct_0 @ (k2_tsep_1 @ X14 @ X13 @ X15))
% 0.59/0.78              = (k3_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15)))
% 0.59/0.78          | ~ (m1_pre_topc @ (k2_tsep_1 @ X14 @ X13 @ X15) @ X14)
% 0.59/0.78          | ~ (v1_pre_topc @ (k2_tsep_1 @ X14 @ X13 @ X15))
% 0.59/0.78          | (v2_struct_0 @ (k2_tsep_1 @ X14 @ X13 @ X15))
% 0.59/0.78          | (r1_tsep_1 @ X13 @ X15)
% 0.59/0.78          | ~ (m1_pre_topc @ X13 @ X14)
% 0.59/0.78          | (v2_struct_0 @ X13))),
% 0.59/0.78      inference('simplify', [status(thm)], ['22'])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['21', '23'])).
% 0.59/0.78  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('simplify', [status(thm)], ['28'])).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '29'])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('simplify', [status(thm)], ['30'])).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (l1_pre_topc @ X18)
% 0.59/0.78          | (v2_struct_0 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X19)
% 0.59/0.78          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.78          | ~ (v2_struct_0 @ (k2_tsep_1 @ X18 @ X17 @ X19)))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.78  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.59/0.78  thf('38', plain,
% 0.59/0.78      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('simplify', [status(thm)], ['37'])).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(d2_subset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_xboole_0 @ A ) =>
% 0.59/0.78         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.59/0.78       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.78         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      (![X6 : $i, X7 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X6 @ X7)
% 0.59/0.78          | (r2_hidden @ X6 @ X7)
% 0.59/0.78          | (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ 
% 0.59/0.78           (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ 
% 0.59/0.78         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['38', '41'])).
% 0.59/0.78  thf(d4_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.59/0.78       ( ![D:$i]:
% 0.59/0.78         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.78           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X4 @ X3)
% 0.59/0.78          | (r2_hidden @ X4 @ X1)
% 0.59/0.78          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.59/0.78         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.78  thf('45', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['42', '44'])).
% 0.59/0.78  thf(fc2_struct_0, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.59/0.78       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.78  thf('46', plain,
% 0.59/0.78      (![X12 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.59/0.78          | ~ (l1_struct_0 @ X12)
% 0.59/0.78          | (v2_struct_0 @ X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.78  thf('47', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.78  thf('48', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['13', '47'])).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('simplify', [status(thm)], ['48'])).
% 0.59/0.78  thf('50', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (l1_pre_topc @ X18)
% 0.59/0.78          | (v2_struct_0 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X19)
% 0.59/0.78          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.78          | ~ (v2_struct_0 @ (k2_tsep_1 @ X18 @ X17 @ X19)))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.78  thf('51', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['49', '50'])).
% 0.59/0.78  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('54', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('55', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.59/0.78  thf('56', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('simplify', [status(thm)], ['55'])).
% 0.59/0.78  thf('57', plain,
% 0.59/0.78      (![X6 : $i, X7 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X6 @ X7)
% 0.59/0.78          | (m1_subset_1 @ X6 @ X7)
% 0.59/0.78          | (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.78  thf('58', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.59/0.78  thf('59', plain,
% 0.59/0.78      (![X20 : $i, X21 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B))
% 0.59/0.78          | ((X20) != (sk_D_1))
% 0.59/0.78          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C))
% 0.59/0.78          | ((X21) != (sk_D_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('60', plain,
% 0.59/0.78      ((![X20 : $i]:
% 0.59/0.78          (((X20) != (sk_D_1)) | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B))))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('split', [status(esa)], ['59'])).
% 0.59/0.78  thf('61', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['60'])).
% 0.59/0.78  thf('62', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.78  thf('63', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ 
% 0.59/0.78         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['38', '41'])).
% 0.59/0.78  thf('64', plain,
% 0.59/0.78      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X4 @ X3)
% 0.59/0.78          | (r2_hidden @ X4 @ X2)
% 0.59/0.78          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.59/0.78  thf('65', plain,
% 0.59/0.78      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.59/0.78         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['64'])).
% 0.59/0.78  thf('66', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['63', '65'])).
% 0.59/0.78  thf('67', plain,
% 0.59/0.78      (![X12 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.59/0.78          | ~ (l1_struct_0 @ X12)
% 0.59/0.78          | (v2_struct_0 @ X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.78  thf('68', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['66', '67'])).
% 0.59/0.78  thf('69', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['62', '68'])).
% 0.59/0.78  thf('70', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('simplify', [status(thm)], ['69'])).
% 0.59/0.78  thf('71', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X17 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (l1_pre_topc @ X18)
% 0.59/0.78          | (v2_struct_0 @ X18)
% 0.59/0.78          | (v2_struct_0 @ X19)
% 0.59/0.78          | ~ (m1_pre_topc @ X19 @ X18)
% 0.59/0.78          | ~ (v2_struct_0 @ (k2_tsep_1 @ X18 @ X17 @ X19)))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.59/0.78  thf('72', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | ~ (l1_pre_topc @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.78  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('76', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.59/0.78  thf('77', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('simplify', [status(thm)], ['76'])).
% 0.59/0.78  thf('78', plain,
% 0.59/0.78      (![X6 : $i, X7 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X6 @ X7)
% 0.59/0.78          | (m1_subset_1 @ X6 @ X7)
% 0.59/0.78          | (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.78  thf('79', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['77', '78'])).
% 0.59/0.78  thf('80', plain,
% 0.59/0.78      ((![X21 : $i]:
% 0.59/0.78          (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C))))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('split', [status(esa)], ['59'])).
% 0.59/0.78  thf('81', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['80'])).
% 0.59/0.78  thf('82', plain,
% 0.59/0.78      ((((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.59/0.78         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['79', '81'])).
% 0.59/0.78  thf('83', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('84', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_C)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_C))))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['82', '83'])).
% 0.59/0.78  thf('85', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X8) | (m1_subset_1 @ X8 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.78  thf('86', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['80'])).
% 0.59/0.78  thf('87', plain,
% 0.59/0.78      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_C)) | ~ (v1_xboole_0 @ sk_D_1)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['85', '86'])).
% 0.59/0.78  thf('88', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['63', '65'])).
% 0.59/0.78  thf('89', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('90', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X8 @ X7) | (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.78  thf('91', plain,
% 0.59/0.78      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.78        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['89', '90'])).
% 0.59/0.78  thf('92', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['88', '91'])).
% 0.59/0.78  thf('93', plain,
% 0.59/0.78      (![X6 : $i, X7 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X6 @ X7)
% 0.59/0.78          | (m1_subset_1 @ X6 @ X7)
% 0.59/0.78          | (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.78  thf('94', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D_1)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.59/0.78        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['92', '93'])).
% 0.59/0.78  thf('95', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['80'])).
% 0.59/0.78  thf('96', plain,
% 0.59/0.78      ((((v1_xboole_0 @ (u1_struct_0 @ sk_C))
% 0.59/0.78         | (v2_struct_0 @ sk_C)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78         | (v1_xboole_0 @ sk_D_1)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['94', '95'])).
% 0.59/0.78  thf('97', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('98', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_D_1)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_C)
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_C))))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['96', '97'])).
% 0.59/0.78  thf('99', plain,
% 0.59/0.78      (![X12 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.59/0.78          | ~ (l1_struct_0 @ X12)
% 0.59/0.78          | (v2_struct_0 @ X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.78  thf('100', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_C)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v1_xboole_0 @ sk_D_1)
% 0.59/0.78         | (v2_struct_0 @ sk_C)
% 0.59/0.78         | ~ (l1_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['98', '99'])).
% 0.59/0.78  thf('101', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('102', plain,
% 0.59/0.78      (![X10 : $i, X11 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X10 @ X11)
% 0.59/0.78          | (l1_pre_topc @ X10)
% 0.59/0.78          | ~ (l1_pre_topc @ X11))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.78  thf('103', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.59/0.78      inference('sup-', [status(thm)], ['101', '102'])).
% 0.59/0.78  thf('104', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('105', plain, ((l1_pre_topc @ sk_C)),
% 0.59/0.78      inference('demod', [status(thm)], ['103', '104'])).
% 0.59/0.78  thf('106', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.78  thf('107', plain, ((l1_struct_0 @ sk_C)),
% 0.59/0.78      inference('sup-', [status(thm)], ['105', '106'])).
% 0.59/0.78  thf('108', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_C)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v1_xboole_0 @ sk_D_1)
% 0.59/0.78         | (v2_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['100', '107'])).
% 0.59/0.78  thf('109', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_D_1)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['108'])).
% 0.59/0.78  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('111', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v1_xboole_0 @ sk_D_1)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['109', '110'])).
% 0.59/0.78  thf('112', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('113', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('clc', [status(thm)], ['111', '112'])).
% 0.59/0.78  thf('114', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('115', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D_1))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('clc', [status(thm)], ['113', '114'])).
% 0.59/0.78  thf('116', plain,
% 0.59/0.78      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['87', '115'])).
% 0.59/0.78  thf('117', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['84', '116'])).
% 0.59/0.78  thf('118', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('119', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('clc', [status(thm)], ['117', '118'])).
% 0.59/0.78  thf('120', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('121', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A))
% 0.59/0.78         <= ((![X21 : $i]:
% 0.59/0.78                (((X21) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C)))))),
% 0.59/0.78      inference('clc', [status(thm)], ['119', '120'])).
% 0.59/0.78  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('123', plain,
% 0.59/0.78      (~
% 0.59/0.78       (![X21 : $i]:
% 0.59/0.78          (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['121', '122'])).
% 0.59/0.78  thf('124', plain,
% 0.59/0.78      ((![X20 : $i]:
% 0.59/0.78          (((X20) != (sk_D_1)) | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))) | 
% 0.59/0.78       (![X21 : $i]:
% 0.59/0.78          (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_C))))),
% 0.59/0.78      inference('split', [status(esa)], ['59'])).
% 0.59/0.78  thf('125', plain,
% 0.59/0.78      ((![X20 : $i]:
% 0.59/0.78          (((X20) != (sk_D_1)) | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B))))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['123', '124'])).
% 0.59/0.78  thf('126', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['61', '125'])).
% 0.59/0.78  thf('127', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('sup-', [status(thm)], ['58', '126'])).
% 0.59/0.78  thf('128', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('129', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['127', '128'])).
% 0.59/0.78  thf('130', plain,
% 0.59/0.78      (![X7 : $i, X8 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X8) | (m1_subset_1 @ X8 @ X7) | ~ (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.78  thf('131', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['60'])).
% 0.59/0.78  thf('132', plain,
% 0.59/0.78      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)) | ~ (v1_xboole_0 @ sk_D_1)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['130', '131'])).
% 0.59/0.78  thf('133', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['42', '44'])).
% 0.59/0.78  thf('134', plain,
% 0.59/0.78      ((~ (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.78        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['89', '90'])).
% 0.59/0.78  thf('135', plain,
% 0.59/0.78      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ sk_D_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['133', '134'])).
% 0.59/0.78  thf('136', plain,
% 0.59/0.78      (![X6 : $i, X7 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X6 @ X7)
% 0.59/0.78          | (m1_subset_1 @ X6 @ X7)
% 0.59/0.78          | (v1_xboole_0 @ X7))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.78  thf('137', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D_1)
% 0.59/0.78        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78        | (v2_struct_0 @ sk_B)
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v2_struct_0 @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.59/0.78        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['135', '136'])).
% 0.59/0.78  thf('138', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['60'])).
% 0.59/0.78  thf('139', plain,
% 0.59/0.78      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.59/0.78         | (v2_struct_0 @ sk_C)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (r1_tsep_1 @ sk_B @ sk_C)
% 0.59/0.78         | (v1_xboole_0 @ sk_D_1)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['137', '138'])).
% 0.59/0.78  thf('140', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('141', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_D_1)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_C)
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_B))))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['139', '140'])).
% 0.59/0.78  thf('142', plain,
% 0.59/0.78      (![X12 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.59/0.78          | ~ (l1_struct_0 @ X12)
% 0.59/0.78          | (v2_struct_0 @ X12))),
% 0.59/0.78      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.78  thf('143', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_C)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v1_xboole_0 @ sk_D_1)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | ~ (l1_struct_0 @ sk_B)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['141', '142'])).
% 0.59/0.78  thf('144', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('145', plain,
% 0.59/0.78      (![X10 : $i, X11 : $i]:
% 0.59/0.78         (~ (m1_pre_topc @ X10 @ X11)
% 0.59/0.78          | (l1_pre_topc @ X10)
% 0.59/0.78          | ~ (l1_pre_topc @ X11))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.78  thf('146', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['144', '145'])).
% 0.59/0.78  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('148', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.78      inference('demod', [status(thm)], ['146', '147'])).
% 0.59/0.78  thf('149', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.78  thf('150', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.78      inference('sup-', [status(thm)], ['148', '149'])).
% 0.59/0.78  thf('151', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_C)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v1_xboole_0 @ sk_D_1)
% 0.59/0.78         | (v2_struct_0 @ sk_B)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['143', '150'])).
% 0.59/0.78  thf('152', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_D_1)
% 0.59/0.78         | (v2_struct_0 @ sk_B)
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v2_struct_0 @ sk_C)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['151'])).
% 0.59/0.78  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('154', plain,
% 0.59/0.78      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B) | (v1_xboole_0 @ sk_D_1)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['152', '153'])).
% 0.59/0.78  thf('155', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('156', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_D_1) | (v2_struct_0 @ sk_B)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('clc', [status(thm)], ['154', '155'])).
% 0.59/0.78  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('158', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D_1))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('clc', [status(thm)], ['156', '157'])).
% 0.59/0.78  thf('159', plain,
% 0.59/0.78      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.59/0.78         <= ((![X20 : $i]:
% 0.59/0.78                (((X20) != (sk_D_1))
% 0.59/0.78                 | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['132', '158'])).
% 0.59/0.78  thf('160', plain,
% 0.59/0.78      ((![X20 : $i]:
% 0.59/0.78          (((X20) != (sk_D_1)) | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ sk_B))))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['123', '124'])).
% 0.59/0.78  thf('161', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['159', '160'])).
% 0.59/0.78  thf('162', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.59/0.78      inference('sup-', [status(thm)], ['129', '161'])).
% 0.59/0.78  thf('163', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('164', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.59/0.78      inference('clc', [status(thm)], ['162', '163'])).
% 0.59/0.78  thf('165', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('166', plain, ((v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('clc', [status(thm)], ['164', '165'])).
% 0.59/0.78  thf('167', plain, ($false), inference('demod', [status(thm)], ['0', '166'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
