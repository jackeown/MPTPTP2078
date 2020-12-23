%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.niAdGLa6RK

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:13 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 299 expanded)
%              Number of leaves         :   26 (  92 expanded)
%              Depth                    :   34
%              Number of atoms          : 1455 (6537 expanded)
%              Number of equality atoms :   36 ( 254 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) @ X19 ) ) ),
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
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( r1_tsep_1 @ X14 @ X16 )
      | ( v2_struct_0 @ X17 )
      | ~ ( v1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ( X17
       != ( k2_tsep_1 @ X15 @ X14 @ X16 ) )
      | ( ( u1_struct_0 @ X17 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X15 @ X14 @ X16 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X15 @ X14 @ X16 ) @ X15 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X15 @ X14 @ X16 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X15 @ X14 @ X16 ) )
      | ( r1_tsep_1 @ X14 @ X16 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
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
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
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
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_B ) )
      | ( X21 != sk_D_1 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) )
      | ( X22 != sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) )
   <= ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_B ) ) ) ),
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
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) ) ) ),
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
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('81',plain,
    ( ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_C ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X21: $i] :
        ( ( X21 != sk_D_1 )
        | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_B ) ) )
    | ! [X22: $i] :
        ( ( X22 != sk_D_1 )
        | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('92',plain,(
    ! [X21: $i] :
      ( ( X21 != sk_D_1 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( m1_subset_1 @ sk_D_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['61','92'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','93'])).

thf('95',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['0','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.niAdGLa6RK
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:28:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.73  % Solved by: fo/fo7.sh
% 0.52/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.73  % done 331 iterations in 0.268s
% 0.52/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.73  % SZS output start Refutation
% 0.52/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.73  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.52/0.73  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.52/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.52/0.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.52/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.73  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.52/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.52/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.52/0.73  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.52/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.73  thf(t17_tmap_1, conjecture,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.73       ( ![B:$i]:
% 0.52/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.52/0.73           ( ![C:$i]:
% 0.52/0.73             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.52/0.73               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.52/0.73                 ( ![D:$i]:
% 0.52/0.73                   ( ( m1_subset_1 @
% 0.52/0.73                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.52/0.73                     ( ( ?[E:$i]:
% 0.52/0.73                         ( ( ( E ) = ( D ) ) & 
% 0.52/0.73                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.52/0.73                       ( ?[E:$i]:
% 0.52/0.73                         ( ( ( E ) = ( D ) ) & 
% 0.52/0.73                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.73    (~( ![A:$i]:
% 0.52/0.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.52/0.73            ( l1_pre_topc @ A ) ) =>
% 0.52/0.73          ( ![B:$i]:
% 0.52/0.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.52/0.73              ( ![C:$i]:
% 0.52/0.73                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.52/0.73                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.52/0.73                    ( ![D:$i]:
% 0.52/0.73                      ( ( m1_subset_1 @
% 0.52/0.73                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.52/0.73                        ( ( ?[E:$i]:
% 0.52/0.73                            ( ( ( E ) = ( D ) ) & 
% 0.52/0.73                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.52/0.73                          ( ?[E:$i]:
% 0.52/0.73                            ( ( ( E ) = ( D ) ) & 
% 0.52/0.73                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.73    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 0.52/0.73  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(dt_k2_tsep_1, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.52/0.73         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.52/0.73         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.52/0.73       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 0.52/0.73         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 0.52/0.73         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.52/0.73  thf('3', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X18)
% 0.52/0.73          | ~ (l1_pre_topc @ X19)
% 0.52/0.73          | (v2_struct_0 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X20)
% 0.52/0.73          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.73          | (m1_pre_topc @ (k2_tsep_1 @ X19 @ X18 @ X20) @ X19))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.52/0.73  thf('4', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.52/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.52/0.73          | (v2_struct_0 @ X0)
% 0.52/0.73          | (v2_struct_0 @ sk_A)
% 0.52/0.73          | ~ (l1_pre_topc @ sk_A)
% 0.52/0.73          | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.73  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('6', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.52/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.52/0.73          | (v2_struct_0 @ X0)
% 0.52/0.73          | (v2_struct_0 @ sk_A)
% 0.52/0.73          | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.52/0.73  thf('7', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['1', '6'])).
% 0.52/0.73  thf(dt_m1_pre_topc, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( l1_pre_topc @ A ) =>
% 0.52/0.73       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.52/0.73  thf('8', plain,
% 0.52/0.73      (![X11 : $i, X12 : $i]:
% 0.52/0.73         (~ (m1_pre_topc @ X11 @ X12)
% 0.52/0.73          | (l1_pre_topc @ X11)
% 0.52/0.73          | ~ (l1_pre_topc @ X12))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.52/0.73  thf('9', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.73        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.73  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('11', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.52/0.73  thf(dt_l1_pre_topc, axiom,
% 0.52/0.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.52/0.73  thf('12', plain,
% 0.52/0.73      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.52/0.73  thf('13', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('16', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X18)
% 0.52/0.73          | ~ (l1_pre_topc @ X19)
% 0.52/0.73          | (v2_struct_0 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X20)
% 0.52/0.73          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.73          | (v1_pre_topc @ (k2_tsep_1 @ X19 @ X18 @ X20)))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.52/0.73  thf('17', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.52/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.52/0.73          | (v2_struct_0 @ X0)
% 0.52/0.73          | (v2_struct_0 @ sk_A)
% 0.52/0.73          | ~ (l1_pre_topc @ sk_A)
% 0.52/0.73          | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.73  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('19', plain,
% 0.52/0.73      (![X0 : $i]:
% 0.52/0.73         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.52/0.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.52/0.73          | (v2_struct_0 @ X0)
% 0.52/0.73          | (v2_struct_0 @ sk_A)
% 0.52/0.73          | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['17', '18'])).
% 0.52/0.73  thf('20', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['14', '19'])).
% 0.52/0.73  thf('21', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['1', '6'])).
% 0.52/0.73  thf(d5_tsep_1, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.52/0.73       ( ![B:$i]:
% 0.52/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.52/0.73           ( ![C:$i]:
% 0.52/0.73             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.52/0.73               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.52/0.73                 ( ![D:$i]:
% 0.52/0.73                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.52/0.73                       ( m1_pre_topc @ D @ A ) ) =>
% 0.52/0.73                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 0.52/0.73                       ( ( u1_struct_0 @ D ) =
% 0.52/0.73                         ( k3_xboole_0 @
% 0.52/0.73                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.73  thf('22', plain,
% 0.52/0.73      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.52/0.73         ((v2_struct_0 @ X14)
% 0.52/0.73          | ~ (m1_pre_topc @ X14 @ X15)
% 0.52/0.73          | (r1_tsep_1 @ X14 @ X16)
% 0.52/0.73          | (v2_struct_0 @ X17)
% 0.52/0.73          | ~ (v1_pre_topc @ X17)
% 0.52/0.73          | ~ (m1_pre_topc @ X17 @ X15)
% 0.52/0.73          | ((X17) != (k2_tsep_1 @ X15 @ X14 @ X16))
% 0.52/0.73          | ((u1_struct_0 @ X17)
% 0.52/0.73              = (k3_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16)))
% 0.52/0.73          | ~ (m1_pre_topc @ X16 @ X15)
% 0.52/0.73          | (v2_struct_0 @ X16)
% 0.52/0.73          | ~ (l1_pre_topc @ X15)
% 0.52/0.73          | (v2_struct_0 @ X15))),
% 0.52/0.73      inference('cnf', [status(esa)], [d5_tsep_1])).
% 0.52/0.73  thf('23', plain,
% 0.52/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.52/0.73         ((v2_struct_0 @ X15)
% 0.52/0.73          | ~ (l1_pre_topc @ X15)
% 0.52/0.73          | (v2_struct_0 @ X16)
% 0.52/0.73          | ~ (m1_pre_topc @ X16 @ X15)
% 0.52/0.73          | ((u1_struct_0 @ (k2_tsep_1 @ X15 @ X14 @ X16))
% 0.52/0.73              = (k3_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16)))
% 0.52/0.73          | ~ (m1_pre_topc @ (k2_tsep_1 @ X15 @ X14 @ X16) @ X15)
% 0.52/0.73          | ~ (v1_pre_topc @ (k2_tsep_1 @ X15 @ X14 @ X16))
% 0.52/0.73          | (v2_struct_0 @ (k2_tsep_1 @ X15 @ X14 @ X16))
% 0.52/0.73          | (r1_tsep_1 @ X14 @ X16)
% 0.52/0.73          | ~ (m1_pre_topc @ X14 @ X15)
% 0.52/0.73          | (v2_struct_0 @ X14))),
% 0.52/0.73      inference('simplify', [status(thm)], ['22'])).
% 0.52/0.73  thf('24', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['21', '23'])).
% 0.52/0.73  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('28', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A))),
% 0.52/0.73      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.52/0.73  thf('29', plain,
% 0.52/0.73      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['28'])).
% 0.52/0.73  thf('30', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['20', '29'])).
% 0.52/0.73  thf('31', plain,
% 0.52/0.73      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['30'])).
% 0.52/0.73  thf('32', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X18)
% 0.52/0.73          | ~ (l1_pre_topc @ X19)
% 0.52/0.73          | (v2_struct_0 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X20)
% 0.52/0.73          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.73          | ~ (v2_struct_0 @ (k2_tsep_1 @ X19 @ X18 @ X20)))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.52/0.73  thf('33', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.73  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('37', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.52/0.73  thf('38', plain,
% 0.52/0.73      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['37'])).
% 0.52/0.73  thf('39', plain,
% 0.52/0.73      ((m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf(t2_subset, axiom,
% 0.52/0.73    (![A:$i,B:$i]:
% 0.52/0.73     ( ( m1_subset_1 @ A @ B ) =>
% 0.52/0.73       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.52/0.73  thf('40', plain,
% 0.52/0.73      (![X8 : $i, X9 : $i]:
% 0.52/0.73         ((r2_hidden @ X8 @ X9)
% 0.52/0.73          | (v1_xboole_0 @ X9)
% 0.52/0.73          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.52/0.73      inference('cnf', [status(esa)], [t2_subset])).
% 0.52/0.73  thf('41', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ 
% 0.52/0.73           (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.73  thf('42', plain,
% 0.52/0.73      (((r2_hidden @ sk_D_1 @ 
% 0.52/0.73         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.52/0.73      inference('sup+', [status(thm)], ['38', '41'])).
% 0.52/0.73  thf(d4_xboole_0, axiom,
% 0.52/0.73    (![A:$i,B:$i,C:$i]:
% 0.52/0.73     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.52/0.73       ( ![D:$i]:
% 0.52/0.73         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.73           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.52/0.73  thf('43', plain,
% 0.52/0.73      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X4 @ X3)
% 0.52/0.73          | (r2_hidden @ X4 @ X1)
% 0.52/0.73          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.52/0.73      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.73  thf('44', plain,
% 0.52/0.73      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.52/0.73         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.52/0.73  thf('45', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['42', '44'])).
% 0.52/0.73  thf(fc2_struct_0, axiom,
% 0.52/0.73    (![A:$i]:
% 0.52/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.52/0.73       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.73  thf('46', plain,
% 0.52/0.73      (![X13 : $i]:
% 0.52/0.73         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.52/0.73          | ~ (l1_struct_0 @ X13)
% 0.52/0.73          | (v2_struct_0 @ X13))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.52/0.73  thf('47', plain,
% 0.52/0.73      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.73  thf('48', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['13', '47'])).
% 0.52/0.73  thf('49', plain,
% 0.52/0.73      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['48'])).
% 0.52/0.73  thf('50', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X18)
% 0.52/0.73          | ~ (l1_pre_topc @ X19)
% 0.52/0.73          | (v2_struct_0 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X20)
% 0.52/0.73          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.73          | ~ (v2_struct_0 @ (k2_tsep_1 @ X19 @ X18 @ X20)))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.52/0.73  thf('51', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['49', '50'])).
% 0.52/0.73  thf('52', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('54', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('55', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.52/0.73  thf('56', plain,
% 0.52/0.73      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_B))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['55'])).
% 0.52/0.73  thf(t1_subset, axiom,
% 0.52/0.73    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.52/0.73  thf('57', plain,
% 0.52/0.73      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t1_subset])).
% 0.52/0.73  thf('58', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['56', '57'])).
% 0.52/0.73  thf('59', plain,
% 0.52/0.73      (![X21 : $i, X22 : $i]:
% 0.52/0.73         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_B))
% 0.52/0.73          | ((X21) != (sk_D_1))
% 0.52/0.73          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C))
% 0.52/0.73          | ((X22) != (sk_D_1)))),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('60', plain,
% 0.52/0.73      ((![X21 : $i]:
% 0.52/0.73          (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_B))))
% 0.52/0.73         <= ((![X21 : $i]:
% 0.52/0.73                (((X21) != (sk_D_1))
% 0.52/0.73                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_B)))))),
% 0.52/0.73      inference('split', [status(esa)], ['59'])).
% 0.52/0.73  thf('61', plain,
% 0.52/0.73      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B)))
% 0.52/0.73         <= ((![X21 : $i]:
% 0.52/0.73                (((X21) != (sk_D_1))
% 0.52/0.73                 | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_B)))))),
% 0.52/0.73      inference('simplify', [status(thm)], ['60'])).
% 0.52/0.73  thf('62', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.73  thf('63', plain,
% 0.52/0.73      (((r2_hidden @ sk_D_1 @ 
% 0.52/0.73         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.52/0.73      inference('sup+', [status(thm)], ['38', '41'])).
% 0.52/0.73  thf('64', plain,
% 0.52/0.73      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.73         (~ (r2_hidden @ X4 @ X3)
% 0.52/0.73          | (r2_hidden @ X4 @ X2)
% 0.52/0.73          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.52/0.73      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.52/0.73  thf('65', plain,
% 0.52/0.73      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.52/0.73         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.52/0.73      inference('simplify', [status(thm)], ['64'])).
% 0.52/0.73  thf('66', plain,
% 0.52/0.73      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['63', '65'])).
% 0.52/0.73  thf('67', plain,
% 0.52/0.73      (![X13 : $i]:
% 0.52/0.73         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.52/0.73          | ~ (l1_struct_0 @ X13)
% 0.52/0.73          | (v2_struct_0 @ X13))),
% 0.52/0.73      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.52/0.73  thf('68', plain,
% 0.52/0.73      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['66', '67'])).
% 0.52/0.73  thf('69', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['62', '68'])).
% 0.52/0.73  thf('70', plain,
% 0.52/0.73      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['69'])).
% 0.52/0.73  thf('71', plain,
% 0.52/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.73         (~ (m1_pre_topc @ X18 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X18)
% 0.52/0.73          | ~ (l1_pre_topc @ X19)
% 0.52/0.73          | (v2_struct_0 @ X19)
% 0.52/0.73          | (v2_struct_0 @ X20)
% 0.52/0.73          | ~ (m1_pre_topc @ X20 @ X19)
% 0.52/0.73          | ~ (v2_struct_0 @ (k2_tsep_1 @ X19 @ X18 @ X20)))),
% 0.52/0.73      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.52/0.73  thf('72', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | ~ (l1_pre_topc @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.52/0.73      inference('sup-', [status(thm)], ['70', '71'])).
% 0.52/0.73  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('76', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.73        | (v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.52/0.73  thf('77', plain,
% 0.52/0.73      (((r2_hidden @ sk_D_1 @ (u1_struct_0 @ sk_C))
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C))),
% 0.52/0.73      inference('simplify', [status(thm)], ['76'])).
% 0.52/0.73  thf('78', plain,
% 0.52/0.73      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.52/0.73      inference('cnf', [status(esa)], [t1_subset])).
% 0.52/0.73  thf('79', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))),
% 0.52/0.73      inference('sup-', [status(thm)], ['77', '78'])).
% 0.52/0.73  thf('80', plain,
% 0.52/0.73      ((![X22 : $i]:
% 0.52/0.73          (((X22) != (sk_D_1)) | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C))))
% 0.52/0.73         <= ((![X22 : $i]:
% 0.52/0.73                (((X22) != (sk_D_1))
% 0.52/0.73                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C)))))),
% 0.52/0.73      inference('split', [status(esa)], ['59'])).
% 0.52/0.73  thf('81', plain,
% 0.52/0.73      ((~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_C)))
% 0.52/0.73         <= ((![X22 : $i]:
% 0.52/0.73                (((X22) != (sk_D_1))
% 0.52/0.73                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C)))))),
% 0.52/0.73      inference('simplify', [status(thm)], ['80'])).
% 0.52/0.73  thf('82', plain,
% 0.52/0.73      ((((r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73         | (v2_struct_0 @ sk_B)
% 0.52/0.73         | (v2_struct_0 @ sk_A)
% 0.52/0.73         | (v2_struct_0 @ sk_C)))
% 0.52/0.73         <= ((![X22 : $i]:
% 0.52/0.73                (((X22) != (sk_D_1))
% 0.52/0.73                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C)))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['79', '81'])).
% 0.52/0.73  thf('83', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('84', plain,
% 0.52/0.73      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 0.52/0.73         <= ((![X22 : $i]:
% 0.52/0.73                (((X22) != (sk_D_1))
% 0.52/0.73                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C)))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['82', '83'])).
% 0.52/0.73  thf('85', plain, (~ (v2_struct_0 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('86', plain,
% 0.52/0.73      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.52/0.73         <= ((![X22 : $i]:
% 0.52/0.73                (((X22) != (sk_D_1))
% 0.52/0.73                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C)))))),
% 0.52/0.73      inference('clc', [status(thm)], ['84', '85'])).
% 0.52/0.73  thf('87', plain, (~ (v2_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('88', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_A))
% 0.52/0.73         <= ((![X22 : $i]:
% 0.52/0.73                (((X22) != (sk_D_1))
% 0.52/0.73                 | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C)))))),
% 0.52/0.73      inference('clc', [status(thm)], ['86', '87'])).
% 0.52/0.73  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('90', plain,
% 0.52/0.73      (~
% 0.52/0.73       (![X22 : $i]:
% 0.52/0.73          (((X22) != (sk_D_1)) | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C))))),
% 0.52/0.73      inference('sup-', [status(thm)], ['88', '89'])).
% 0.52/0.73  thf('91', plain,
% 0.52/0.73      ((![X21 : $i]:
% 0.52/0.73          (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_B)))) | 
% 0.52/0.73       (![X22 : $i]:
% 0.52/0.73          (((X22) != (sk_D_1)) | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ sk_C))))),
% 0.52/0.73      inference('split', [status(esa)], ['59'])).
% 0.52/0.73  thf('92', plain,
% 0.52/0.73      ((![X21 : $i]:
% 0.52/0.73          (((X21) != (sk_D_1)) | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ sk_B))))),
% 0.52/0.73      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.52/0.73  thf('93', plain, (~ (m1_subset_1 @ sk_D_1 @ (u1_struct_0 @ sk_B))),
% 0.52/0.73      inference('simpl_trail', [status(thm)], ['61', '92'])).
% 0.52/0.73  thf('94', plain,
% 0.52/0.73      (((r1_tsep_1 @ sk_B @ sk_C)
% 0.52/0.73        | (v2_struct_0 @ sk_B)
% 0.52/0.73        | (v2_struct_0 @ sk_A)
% 0.52/0.73        | (v2_struct_0 @ sk_C))),
% 0.52/0.73      inference('sup-', [status(thm)], ['58', '93'])).
% 0.52/0.73  thf('95', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('96', plain,
% 0.52/0.73      (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B))),
% 0.52/0.73      inference('sup-', [status(thm)], ['94', '95'])).
% 0.52/0.73  thf('97', plain, (~ (v2_struct_0 @ sk_C)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('98', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.52/0.73      inference('clc', [status(thm)], ['96', '97'])).
% 0.52/0.73  thf('99', plain, (~ (v2_struct_0 @ sk_B)),
% 0.52/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.73  thf('100', plain, ((v2_struct_0 @ sk_A)),
% 0.52/0.73      inference('clc', [status(thm)], ['98', '99'])).
% 0.52/0.73  thf('101', plain, ($false), inference('demod', [status(thm)], ['0', '100'])).
% 0.52/0.73  
% 0.52/0.73  % SZS output end Refutation
% 0.52/0.73  
% 0.52/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
