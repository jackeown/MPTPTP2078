%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nIjP0uEGp4

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:03 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 147 expanded)
%              Number of leaves         :   37 (  60 expanded)
%              Depth                    :   21
%              Number of atoms          :  662 (1731 expanded)
%              Number of equality atoms :   29 (  62 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t50_subset_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ ( k3_subset_1 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r2_hidden @ X2 @ ( k3_subset_1 @ X0 @ ( k1_subset_1 @ X1 ) ) )
      | ( r2_hidden @ X2 @ ( k1_subset_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('12',plain,(
    ! [X4: $i] :
      ( X4
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_subset_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B_1 @ ( k1_subset_1 @ X0 ) )
      | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ ( k1_subset_1 @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_subset_1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('22',plain,(
    ! [X19: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('24',plain,(
    ! [X18: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('25',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X21: $i] :
      ( ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( v4_pre_topc @ X21 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X21 )
      | ( r2_hidden @ X21 @ sk_C )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X21: $i] :
      ( ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( v4_pre_topc @ X21 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X21 )
      | ( r2_hidden @ X21 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('35',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('44',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','48'])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

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

thf('54',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ ( sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X20 ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nIjP0uEGp4
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 293 iterations in 0.115s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.36/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.58  thf(t28_connsp_2, conjecture,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.58           ( ![C:$i]:
% 0.36/0.58             ( ( m1_subset_1 @
% 0.36/0.58                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.58               ( ~( ( ![D:$i]:
% 0.36/0.58                      ( ( m1_subset_1 @
% 0.36/0.58                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.58                        ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.58                          ( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.58                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.36/0.58                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i]:
% 0.36/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.58            ( l1_pre_topc @ A ) ) =>
% 0.36/0.58          ( ![B:$i]:
% 0.36/0.58            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.58              ( ![C:$i]:
% 0.36/0.58                ( ( m1_subset_1 @
% 0.36/0.58                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.58                  ( ~( ( ![D:$i]:
% 0.36/0.58                         ( ( m1_subset_1 @
% 0.36/0.58                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.58                           ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.58                             ( ( v3_pre_topc @ D @ A ) & 
% 0.36/0.58                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.36/0.58                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.36/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.58  thf('2', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.36/0.58  thf(t4_subset_1, axiom,
% 0.36/0.58    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.36/0.58      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf(t50_subset_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58           ( ![C:$i]:
% 0.36/0.58             ( ( m1_subset_1 @ C @ A ) =>
% 0.36/0.58               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.36/0.58                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.36/0.58          | (r2_hidden @ X8 @ X6)
% 0.36/0.58          | (r2_hidden @ X8 @ (k3_subset_1 @ X7 @ X6))
% 0.36/0.58          | ~ (m1_subset_1 @ X8 @ X7)
% 0.36/0.58          | ((X7) = (k1_xboole_0)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (((X0) = (k1_xboole_0))
% 0.36/0.58          | ~ (m1_subset_1 @ X2 @ X0)
% 0.36/0.58          | (r2_hidden @ X2 @ (k3_subset_1 @ X0 @ (k1_subset_1 @ X1)))
% 0.36/0.58          | (r2_hidden @ X2 @ (k1_subset_1 @ X1)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.58  thf('7', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.36/0.58  thf('8', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 0.36/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.36/0.58  thf(t22_subset_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X4 : $i]:
% 0.36/0.58         ((k2_subset_1 @ X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.36/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.58  thf('11', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X4 : $i]: ((X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.36/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['9', '12'])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (((X0) = (k1_xboole_0))
% 0.36/0.58          | ~ (m1_subset_1 @ X2 @ X0)
% 0.36/0.58          | (r2_hidden @ X2 @ X0)
% 0.36/0.58          | (r2_hidden @ X2 @ (k1_subset_1 @ X1)))),
% 0.36/0.58      inference('demod', [status(thm)], ['6', '13'])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((r2_hidden @ sk_B_1 @ (k1_subset_1 @ X0))
% 0.36/0.58          | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58          | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['1', '14'])).
% 0.36/0.58  thf(t7_ordinal1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X14 : $i, X15 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.36/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.58          | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58          | ~ (r1_tarski @ (k1_subset_1 @ X0) @ sk_B_1))),
% 0.36/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.58  thf('18', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.36/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.58  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k1_subset_1 @ X0) @ X1)),
% 0.36/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.58        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('demod', [status(thm)], ['17', '20'])).
% 0.36/0.58  thf(fc10_tops_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X19 : $i]:
% 0.36/0.58         ((v3_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.36/0.58          | ~ (l1_pre_topc @ X19)
% 0.36/0.58          | ~ (v2_pre_topc @ X19))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.36/0.58  thf(d3_struct_0, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X16 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf(fc4_pre_topc, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         ((v4_pre_topc @ (k2_struct_0 @ X18) @ X18)
% 0.36/0.58          | ~ (l1_pre_topc @ X18)
% 0.36/0.58          | ~ (v2_pre_topc @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (![X16 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf(dt_k2_subset_1, axiom,
% 0.36/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.36/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.58  thf('27', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.58  thf('28', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.36/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      (![X21 : $i]:
% 0.36/0.58         (~ (v3_pre_topc @ X21 @ sk_A)
% 0.36/0.58          | ~ (v4_pre_topc @ X21 @ sk_A)
% 0.36/0.58          | ~ (r2_hidden @ sk_B_1 @ X21)
% 0.36/0.58          | (r2_hidden @ X21 @ sk_C)
% 0.36/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('30', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (![X21 : $i]:
% 0.36/0.58         (~ (v3_pre_topc @ X21 @ sk_A)
% 0.36/0.58          | ~ (v4_pre_topc @ X21 @ sk_A)
% 0.36/0.58          | ~ (r2_hidden @ sk_B_1 @ X21)
% 0.36/0.58          | (r2_hidden @ X21 @ k1_xboole_0)
% 0.36/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['28', '31'])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['25', '32'])).
% 0.36/0.58  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(dt_l1_pre_topc, axiom,
% 0.36/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.36/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.58  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['33', '36'])).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['24', '37'])).
% 0.36/0.58  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['23', '41'])).
% 0.36/0.58  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['42', '43'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['22', '44'])).
% 0.36/0.58  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['21', '48'])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      (![X14 : $i, X15 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.36/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.36/0.58        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.58  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.36/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.58  thf('53', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.36/0.58  thf(rc3_tops_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( ?[B:$i]:
% 0.36/0.58         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.36/0.58           ( ~( v1_xboole_0 @ B ) ) & 
% 0.36/0.58           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.58  thf('54', plain,
% 0.36/0.58      (![X20 : $i]:
% 0.36/0.58         ((m1_subset_1 @ (sk_B @ X20) @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.58          | ~ (l1_pre_topc @ X20)
% 0.36/0.58          | ~ (v2_pre_topc @ X20)
% 0.36/0.58          | (v2_struct_0 @ X20))),
% 0.36/0.58      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.36/0.58  thf(cc1_subset_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.58  thf('55', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.36/0.58          | (v1_xboole_0 @ X9)
% 0.36/0.58          | ~ (v1_xboole_0 @ X10))),
% 0.36/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.58  thf('56', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((v2_struct_0 @ X0)
% 0.36/0.58          | ~ (v2_pre_topc @ X0)
% 0.36/0.58          | ~ (l1_pre_topc @ X0)
% 0.36/0.58          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.36/0.58          | (v1_xboole_0 @ (sk_B @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['54', '55'])).
% 0.36/0.58  thf('57', plain,
% 0.36/0.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.58        | (v1_xboole_0 @ (sk_B @ sk_A))
% 0.36/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.58        | (v2_struct_0 @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['53', '56'])).
% 0.36/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.58  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('61', plain, (((v1_xboole_0 @ (sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.36/0.58  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('63', plain, ((v1_xboole_0 @ (sk_B @ sk_A))),
% 0.36/0.58      inference('clc', [status(thm)], ['61', '62'])).
% 0.36/0.58  thf('64', plain,
% 0.36/0.58      (![X20 : $i]:
% 0.36/0.58         (~ (v1_xboole_0 @ (sk_B @ X20))
% 0.36/0.58          | ~ (l1_pre_topc @ X20)
% 0.36/0.58          | ~ (v2_pre_topc @ X20)
% 0.36/0.58          | (v2_struct_0 @ X20))),
% 0.36/0.58      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.36/0.58  thf('65', plain,
% 0.36/0.58      (((v2_struct_0 @ sk_A) | ~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.58  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('68', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.58      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.36/0.58  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
