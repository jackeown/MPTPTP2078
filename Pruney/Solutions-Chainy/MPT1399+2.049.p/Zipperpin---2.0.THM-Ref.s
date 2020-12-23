%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UIoaBhXdol

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 283 expanded)
%              Number of leaves         :   41 ( 101 expanded)
%              Depth                    :   22
%              Number of atoms          :  726 (3809 expanded)
%              Number of equality atoms :   49 ( 153 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('4',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t50_subset_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ ( k3_subset_1 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('7',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r2_hidden @ X8 @ X6 )
      | ( r2_hidden @ X8 @ ( k3_subset_1 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( X7 = sk_C ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_subset_1 @ X0 @ sk_C ) )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('11',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X4: $i] :
      ( X4
      = ( k3_subset_1 @ X4 @ ( k1_subset_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = sk_C )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('19',plain,(
    ! [X20: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X19: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('24',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('25',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X23: $i] :
      ( ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( v4_pre_topc @ X23 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X23 )
      | ( r2_hidden @ X23 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('30',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ( r2_hidden @ sk_B_1 @ sk_C )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['18','43'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('46',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('48',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_C )
    | ~ ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['55','56'])).

thf(fc14_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ~ ( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('58',plain,(
    ! [X22: $i] :
      ( ~ ( v2_tops_1 @ ( k2_struct_0 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc14_tops_1])).

thf('59',plain,
    ( ~ ( v2_tops_1 @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v2_tops_1 @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf(rc5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v2_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc5_tops_1])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X14 ) @ X13 )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ X0 ) ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k9_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( sk_B @ sk_A ) )
      = ( sk_B @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('68',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('69',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k6_relat_1 @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['68','69','70'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('72',plain,(
    ! [X12: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('73',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X12: $i] :
      ( ( k9_relat_1 @ sk_C @ X12 )
      = sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( sk_C
    = ( sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','71','75','76'])).

thf('78',plain,(
    ! [X21: $i] :
      ( ( v2_tops_1 @ ( sk_B @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc5_tops_1])).

thf('79',plain,
    ( ( v2_tops_1 @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v2_tops_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['62','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UIoaBhXdol
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:02:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 373 iterations in 0.092s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.55  thf(t28_connsp_2, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @
% 0.20/0.55                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55               ( ~( ( ![D:$i]:
% 0.20/0.55                      ( ( m1_subset_1 @
% 0.20/0.55                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                        ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55                          ( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.55                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.55                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.55            ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( m1_subset_1 @
% 0.20/0.55                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55                  ( ~( ( ![D:$i]:
% 0.20/0.55                         ( ( m1_subset_1 @
% 0.20/0.55                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55                           ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55                             ( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.55                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.20/0.55                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.20/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d3_struct_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X17 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t4_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.55  thf('4', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('5', plain, (![X5 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X5))),
% 0.20/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.55  thf(t50_subset_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.55               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.20/0.55                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.55          | (r2_hidden @ X8 @ X6)
% 0.20/0.55          | (r2_hidden @ X8 @ (k3_subset_1 @ X7 @ X6))
% 0.20/0.55          | ~ (m1_subset_1 @ X8 @ X7)
% 0.20/0.55          | ((X7) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.20/0.55  thf('7', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.55          | (r2_hidden @ X8 @ X6)
% 0.20/0.55          | (r2_hidden @ X8 @ (k3_subset_1 @ X7 @ X6))
% 0.20/0.55          | ~ (m1_subset_1 @ X8 @ X7)
% 0.20/0.55          | ((X7) = (sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((X0) = (sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.55          | (r2_hidden @ X1 @ (k3_subset_1 @ X0 @ sk_C))
% 0.20/0.55          | (r2_hidden @ X1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.55  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('10', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.55  thf('11', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('12', plain, (![X1 : $i]: ((k1_subset_1 @ X1) = (sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf(t22_subset_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X4 : $i]:
% 0.20/0.55         ((k2_subset_1 @ X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.20/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.55  thf('14', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X4 : $i]: ((X4) = (k3_subset_1 @ X4 @ (k1_subset_1 @ X4)))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ sk_C))),
% 0.20/0.55      inference('sup+', [status(thm)], ['12', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((X0) = (sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ X0)
% 0.20/0.55          | (r2_hidden @ X1 @ X0)
% 0.20/0.55          | (r2_hidden @ X1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (((r2_hidden @ sk_B_1 @ sk_C)
% 0.20/0.55        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '17'])).
% 0.20/0.55  thf(fc10_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X20 : $i]:
% 0.20/0.55         ((v3_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 0.20/0.55          | ~ (l1_pre_topc @ X20)
% 0.20/0.55          | ~ (v2_pre_topc @ X20))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X17 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf(fc4_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X19 : $i]:
% 0.20/0.55         ((v4_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.20/0.55          | ~ (l1_pre_topc @ X19)
% 0.20/0.55          | ~ (v2_pre_topc @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X17 : $i]:
% 0.20/0.55         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.55  thf(dt_k2_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.55  thf('24', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('25', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.20/0.55      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X23 : $i]:
% 0.20/0.55         (~ (v3_pre_topc @ X23 @ sk_A)
% 0.20/0.55          | ~ (v4_pre_topc @ X23 @ sk_A)
% 0.20/0.55          | ~ (r2_hidden @ sk_B_1 @ X23)
% 0.20/0.55          | (r2_hidden @ X23 @ sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '27'])).
% 0.20/0.55  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_l1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['28', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '32'])).
% 0.20/0.55  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '36'])).
% 0.20/0.55  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '39'])).
% 0.20/0.55  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.20/0.55        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      ((((u1_struct_0 @ sk_A) = (sk_C))
% 0.20/0.55        | (r2_hidden @ sk_B_1 @ sk_C)
% 0.20/0.55        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '43'])).
% 0.20/0.55  thf(t7_ordinal1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (((r2_hidden @ sk_B_1 @ sk_C)
% 0.20/0.55        | ((u1_struct_0 @ sk_A) = (sk_C))
% 0.20/0.55        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('48', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('49', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (((r2_hidden @ sk_B_1 @ sk_C) | ((u1_struct_0 @ sk_A) = (sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['46', '49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      ((((u1_struct_0 @ sk_A) = (sk_C)) | ~ (r1_tarski @ sk_C @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf('53', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('54', plain, (((u1_struct_0 @ sk_A) = (sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      ((((k2_struct_0 @ sk_A) = (sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['1', '54'])).
% 0.20/0.55  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('57', plain, (((k2_struct_0 @ sk_A) = (sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.55  thf(fc14_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ~( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X22 : $i]:
% 0.20/0.55         (~ (v2_tops_1 @ (k2_struct_0 @ X22) @ X22)
% 0.20/0.55          | ~ (l1_pre_topc @ X22)
% 0.20/0.55          | ~ (v2_pre_topc @ X22)
% 0.20/0.55          | (v2_struct_0 @ X22))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc14_tops_1])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      ((~ (v2_tops_1 @ sk_C @ sk_A)
% 0.20/0.55        | (v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.55  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('62', plain, ((~ (v2_tops_1 @ sk_C @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.55  thf('63', plain, (((u1_struct_0 @ sk_A) = (sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf(rc5_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ?[B:$i]:
% 0.20/0.55         ( ( v2_tops_1 @ B @ A ) & 
% 0.20/0.55           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X21 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (sk_B @ X21) @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.55          | ~ (l1_pre_topc @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [rc5_tops_1])).
% 0.20/0.55  thf(t162_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (((k9_relat_1 @ (k6_relat_1 @ X14) @ X13) = (X13))
% 0.20/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X0)
% 0.20/0.55          | ((k9_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ X0)) @ (sk_B @ X0))
% 0.20/0.55              = (sk_B @ X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      ((((k9_relat_1 @ (k6_relat_1 @ sk_C) @ (sk_B @ sk_A)) = (sk_B @ sk_A))
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['63', '66'])).
% 0.20/0.55  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.55  thf('68', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.55  thf('69', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('70', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('71', plain, (((k6_relat_1 @ sk_C) = (sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.20/0.55  thf(t150_relat_1, axiom,
% 0.20/0.55    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X12 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.20/0.55  thf('73', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('75', plain, (![X12 : $i]: ((k9_relat_1 @ sk_C @ X12) = (sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.20/0.55  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('77', plain, (((sk_C) = (sk_B @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['67', '71', '75', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (![X21 : $i]: ((v2_tops_1 @ (sk_B @ X21) @ X21) | ~ (l1_pre_topc @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [rc5_tops_1])).
% 0.20/0.55  thf('79', plain, (((v2_tops_1 @ sk_C @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup+', [status(thm)], ['77', '78'])).
% 0.20/0.55  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('81', plain, ((v2_tops_1 @ sk_C @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.55  thf('82', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['62', '81'])).
% 0.20/0.55  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
