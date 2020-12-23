%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LnVabc5bUN

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:12 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 308 expanded)
%              Number of leaves         :   30 (  97 expanded)
%              Depth                    :   33
%              Number of atoms          : 1472 (6556 expanded)
%              Number of equality atoms :   35 ( 252 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X23 @ X22 @ X24 ) @ X23 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( l1_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_pre_topc @ ( k2_tsep_1 @ X23 @ X22 @ X24 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tsep_1 @ X18 @ X20 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_pre_topc @ X21 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( X21
       != ( k2_tsep_1 @ X19 @ X18 @ X20 ) )
      | ( ( u1_struct_0 @ X21 )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_tsep_1])).

thf('23',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( ( u1_struct_0 @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) )
        = ( k3_xboole_0 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) @ X19 )
      | ~ ( v1_pre_topc @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) )
      | ( v2_struct_0 @ ( k2_tsep_1 @ X19 @ X18 @ X20 ) )
      | ( r1_tsep_1 @ X18 @ X20 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X23 @ X22 @ X24 ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r2_hidden @ sk_D @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('49',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','50'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X23 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_B ) )
      | ( X25 != sk_D )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) )
      | ( X26 != sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ! [X25: $i] :
        ( ( X25 != sk_D )
        | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_B ) ) )
   <= ! [X25: $i] :
        ( ( X25 != sk_D )
        | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) )
   <= ! [X25: $i] :
        ( ( X25 != sk_D )
        | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('64',plain,
    ( ( r2_hidden @ sk_D @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( v2_struct_0 @ ( k2_tsep_1 @ X23 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,
    ( ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) )
   <= ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_C ) )
   <= ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ~ ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ! [X25: $i] :
        ( ( X25 != sk_D )
        | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_B ) ) )
    | ! [X26: $i] :
        ( ( X26 != sk_D )
        | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('96',plain,(
    ! [X25: $i] :
      ( ( X25 != sk_D )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['62','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','97'])).

thf('99',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['0','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LnVabc5bUN
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 198 iterations in 0.177s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.63  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 0.45/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.45/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(t17_tmap_1, conjecture,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.45/0.63                 ( ![D:$i]:
% 0.45/0.63                   ( ( m1_subset_1 @
% 0.45/0.63                       D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.45/0.63                     ( ( ?[E:$i]:
% 0.45/0.63                         ( ( ( E ) = ( D ) ) & 
% 0.45/0.63                           ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.45/0.63                       ( ?[E:$i]:
% 0.45/0.63                         ( ( ( E ) = ( D ) ) & 
% 0.45/0.63                           ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i]:
% 0.45/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.63            ( l1_pre_topc @ A ) ) =>
% 0.45/0.63          ( ![B:$i]:
% 0.45/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.63              ( ![C:$i]:
% 0.45/0.63                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63                  ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.45/0.63                    ( ![D:$i]:
% 0.45/0.63                      ( ( m1_subset_1 @
% 0.45/0.63                          D @ ( u1_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 0.45/0.63                        ( ( ?[E:$i]:
% 0.45/0.63                            ( ( ( E ) = ( D ) ) & 
% 0.45/0.63                              ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 0.45/0.63                          ( ?[E:$i]:
% 0.45/0.63                            ( ( ( E ) = ( D ) ) & 
% 0.45/0.63                              ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t17_tmap_1])).
% 0.45/0.63  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(dt_k2_tsep_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.45/0.63         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 0.45/0.63         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 0.45/0.63         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 0.45/0.63         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X22 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (l1_pre_topc @ X23)
% 0.45/0.63          | (v2_struct_0 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X24)
% 0.45/0.63          | ~ (m1_pre_topc @ X24 @ X23)
% 0.45/0.63          | (m1_pre_topc @ (k2_tsep_1 @ X23 @ X22 @ X24) @ X23))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.63  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '6'])).
% 0.45/0.63  thf(dt_m1_pre_topc, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( l1_pre_topc @ A ) =>
% 0.45/0.63       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X15 : $i, X16 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X15 @ X16)
% 0.45/0.63          | (l1_pre_topc @ X15)
% 0.45/0.63          | ~ (l1_pre_topc @ X16))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf(dt_l1_pre_topc, axiom,
% 0.45/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf('14', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X22 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (l1_pre_topc @ X23)
% 0.45/0.63          | (v2_struct_0 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X24)
% 0.45/0.63          | ~ (m1_pre_topc @ X24 @ X23)
% 0.45/0.63          | (v1_pre_topc @ (k2_tsep_1 @ X23 @ X22 @ X24)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.63  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0))
% 0.45/0.63          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ X0)
% 0.45/0.63          | (v2_struct_0 @ sk_A)
% 0.45/0.63          | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['1', '6'])).
% 0.45/0.63  thf(d5_tsep_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.45/0.63               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 0.45/0.63                 ( ![D:$i]:
% 0.45/0.63                   ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.45/0.63                       ( m1_pre_topc @ D @ A ) ) =>
% 0.45/0.63                     ( ( ( D ) = ( k2_tsep_1 @ A @ B @ C ) ) <=>
% 0.45/0.63                       ( ( u1_struct_0 @ D ) =
% 0.45/0.63                         ( k3_xboole_0 @
% 0.45/0.63                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X18)
% 0.45/0.63          | ~ (m1_pre_topc @ X18 @ X19)
% 0.45/0.63          | (r1_tsep_1 @ X18 @ X20)
% 0.45/0.63          | (v2_struct_0 @ X21)
% 0.45/0.63          | ~ (v1_pre_topc @ X21)
% 0.45/0.63          | ~ (m1_pre_topc @ X21 @ X19)
% 0.45/0.63          | ((X21) != (k2_tsep_1 @ X19 @ X18 @ X20))
% 0.45/0.63          | ((u1_struct_0 @ X21)
% 0.45/0.63              = (k3_xboole_0 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20)))
% 0.45/0.63          | ~ (m1_pre_topc @ X20 @ X19)
% 0.45/0.63          | (v2_struct_0 @ X20)
% 0.45/0.63          | ~ (l1_pre_topc @ X19)
% 0.45/0.63          | (v2_struct_0 @ X19))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_tsep_1])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.63         ((v2_struct_0 @ X19)
% 0.45/0.63          | ~ (l1_pre_topc @ X19)
% 0.45/0.63          | (v2_struct_0 @ X20)
% 0.45/0.63          | ~ (m1_pre_topc @ X20 @ X19)
% 0.45/0.63          | ((u1_struct_0 @ (k2_tsep_1 @ X19 @ X18 @ X20))
% 0.45/0.63              = (k3_xboole_0 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20)))
% 0.45/0.63          | ~ (m1_pre_topc @ (k2_tsep_1 @ X19 @ X18 @ X20) @ X19)
% 0.45/0.63          | ~ (v1_pre_topc @ (k2_tsep_1 @ X19 @ X18 @ X20))
% 0.45/0.63          | (v2_struct_0 @ (k2_tsep_1 @ X19 @ X18 @ X20))
% 0.45/0.63          | (r1_tsep_1 @ X18 @ X20)
% 0.45/0.63          | ~ (m1_pre_topc @ X18 @ X19)
% 0.45/0.63          | (v2_struct_0 @ X18))),
% 0.45/0.63      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['21', '23'])).
% 0.45/0.63  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | ~ (v1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '29'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X22 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (l1_pre_topc @ X23)
% 0.45/0.63          | (v2_struct_0 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X24)
% 0.45/0.63          | ~ (m1_pre_topc @ X24 @ X23)
% 0.45/0.63          | ~ (v2_struct_0 @ (k2_tsep_1 @ X23 @ X22 @ X24)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.63  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('36', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | ((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63            = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      ((((u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_D @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t2_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X6 : $i, X7 : $i]:
% 0.45/0.63         ((r2_hidden @ X6 @ X7)
% 0.45/0.63          | (v1_xboole_0 @ X7)
% 0.45/0.63          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.45/0.63      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.45/0.63        | (r2_hidden @ sk_D @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (((r2_hidden @ sk_D @ 
% 0.45/0.63         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['38', '41'])).
% 0.45/0.63  thf(t17_xboole_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.45/0.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.63  thf(t3_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (![X8 : $i, X10 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.63  thf(t4_subset, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.63       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X11 @ X12)
% 0.45/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.45/0.63          | (m1_subset_1 @ X11 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X2 @ X0)
% 0.45/0.63          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['42', '47'])).
% 0.45/0.63  thf(fc2_struct_0, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.63       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      (![X17 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.45/0.63          | ~ (l1_struct_0 @ X17)
% 0.45/0.63          | (v2_struct_0 @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '50'])).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X22 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (l1_pre_topc @ X23)
% 0.45/0.63          | (v2_struct_0 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X24)
% 0.45/0.63          | ~ (m1_pre_topc @ X24 @ X23)
% 0.45/0.63          | ~ (v2_struct_0 @ (k2_tsep_1 @ X23 @ X22 @ X24)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.63  thf('55', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('58', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.45/0.63  thf('59', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['58'])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      (![X25 : $i, X26 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_B))
% 0.45/0.63          | ((X25) != (sk_D))
% 0.45/0.63          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C))
% 0.45/0.63          | ((X26) != (sk_D)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      ((![X25 : $i]:
% 0.45/0.63          (((X25) != (sk_D)) | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_B))))
% 0.45/0.63         <= ((![X25 : $i]:
% 0.45/0.63                (((X25) != (sk_D))
% 0.45/0.63                 | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.63      inference('split', [status(esa)], ['60'])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B)))
% 0.45/0.63         <= ((![X25 : $i]:
% 0.45/0.63                (((X25) != (sk_D))
% 0.45/0.63                 | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_B)))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['61'])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.63  thf('64', plain,
% 0.45/0.63      (((r2_hidden @ sk_D @ 
% 0.45/0.63         (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 0.45/0.63      inference('sup+', [status(thm)], ['38', '41'])).
% 0.45/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.63  thf('66', plain,
% 0.45/0.63      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.45/0.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.45/0.63  thf('67', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.45/0.63      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.63  thf('68', plain,
% 0.45/0.63      (![X8 : $i, X10 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.45/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['67', '68'])).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X11 @ X12)
% 0.45/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.45/0.63          | (m1_subset_1 @ X11 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         ((m1_subset_1 @ X2 @ X0)
% 0.45/0.63          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.63  thf('72', plain,
% 0.45/0.63      (((v1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['64', '71'])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      (![X17 : $i]:
% 0.45/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.45/0.63          | ~ (l1_struct_0 @ X17)
% 0.45/0.63          | (v2_struct_0 @ X17))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.63  thf('74', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.63  thf('75', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['63', '74'])).
% 0.45/0.63  thf('76', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['75'])).
% 0.45/0.63  thf('77', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (~ (m1_pre_topc @ X22 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X22)
% 0.45/0.63          | ~ (l1_pre_topc @ X23)
% 0.45/0.63          | (v2_struct_0 @ X23)
% 0.45/0.63          | (v2_struct_0 @ X24)
% 0.45/0.63          | ~ (m1_pre_topc @ X24 @ X23)
% 0.45/0.63          | ~ (v2_struct_0 @ (k2_tsep_1 @ X23 @ X22 @ X24)))),
% 0.45/0.63      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 0.45/0.63  thf('78', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 0.45/0.63      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.63  thf('79', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('82', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B))),
% 0.45/0.63      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.45/0.63  thf('83', plain,
% 0.45/0.63      (((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C))
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('simplify', [status(thm)], ['82'])).
% 0.45/0.63  thf('84', plain,
% 0.45/0.63      ((![X26 : $i]:
% 0.45/0.63          (((X26) != (sk_D)) | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C))))
% 0.45/0.63         <= ((![X26 : $i]:
% 0.45/0.63                (((X26) != (sk_D))
% 0.45/0.63                 | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C)))))),
% 0.45/0.63      inference('split', [status(esa)], ['60'])).
% 0.45/0.63  thf('85', plain,
% 0.45/0.63      ((~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.45/0.63         <= ((![X26 : $i]:
% 0.45/0.63                (((X26) != (sk_D))
% 0.45/0.63                 | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C)))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['84'])).
% 0.45/0.63  thf('86', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_C)
% 0.45/0.63         | (v2_struct_0 @ sk_A)
% 0.45/0.63         | (v2_struct_0 @ sk_B)
% 0.45/0.63         | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.45/0.63         <= ((![X26 : $i]:
% 0.45/0.63                (((X26) != (sk_D))
% 0.45/0.63                 | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['83', '85'])).
% 0.45/0.63  thf('87', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('88', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.45/0.63         <= ((![X26 : $i]:
% 0.45/0.63                (((X26) != (sk_D))
% 0.45/0.63                 | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C)))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['86', '87'])).
% 0.45/0.63  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('90', plain,
% 0.45/0.63      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.45/0.63         <= ((![X26 : $i]:
% 0.45/0.63                (((X26) != (sk_D))
% 0.45/0.63                 | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C)))))),
% 0.45/0.63      inference('clc', [status(thm)], ['88', '89'])).
% 0.45/0.63  thf('91', plain, (~ (v2_struct_0 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('92', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_A))
% 0.45/0.63         <= ((![X26 : $i]:
% 0.45/0.63                (((X26) != (sk_D))
% 0.45/0.63                 | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C)))))),
% 0.45/0.63      inference('clc', [status(thm)], ['90', '91'])).
% 0.45/0.63  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('94', plain,
% 0.45/0.63      (~
% 0.45/0.63       (![X26 : $i]:
% 0.45/0.63          (((X26) != (sk_D)) | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['92', '93'])).
% 0.45/0.63  thf('95', plain,
% 0.45/0.63      ((![X25 : $i]:
% 0.45/0.63          (((X25) != (sk_D)) | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_B)))) | 
% 0.45/0.63       (![X26 : $i]:
% 0.45/0.63          (((X26) != (sk_D)) | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ sk_C))))),
% 0.45/0.63      inference('split', [status(esa)], ['60'])).
% 0.45/0.63  thf('96', plain,
% 0.45/0.63      ((![X25 : $i]:
% 0.45/0.63          (((X25) != (sk_D)) | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ sk_B))))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 0.45/0.63  thf('97', plain, (~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['62', '96'])).
% 0.45/0.63  thf('98', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_C)
% 0.45/0.63        | (v2_struct_0 @ sk_A)
% 0.45/0.63        | (v2_struct_0 @ sk_B)
% 0.45/0.63        | (r1_tsep_1 @ sk_B @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['59', '97'])).
% 0.45/0.63  thf('99', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('100', plain,
% 0.45/0.63      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.45/0.63      inference('sup-', [status(thm)], ['98', '99'])).
% 0.45/0.63  thf('101', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('102', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.45/0.63      inference('clc', [status(thm)], ['100', '101'])).
% 0.45/0.63  thf('103', plain, (~ (v2_struct_0 @ sk_C)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('104', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.63      inference('clc', [status(thm)], ['102', '103'])).
% 0.45/0.63  thf('105', plain, ($false), inference('demod', [status(thm)], ['0', '104'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
