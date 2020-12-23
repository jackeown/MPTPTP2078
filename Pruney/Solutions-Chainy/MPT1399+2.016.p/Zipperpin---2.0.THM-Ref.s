%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rkfb65zL50

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 147 expanded)
%              Number of leaves         :   40 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  601 (1785 expanded)
%              Number of equality atoms :   26 (  60 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('5',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ sk_C )
      | ( v4_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_C ) @ X0 )
      | ~ ( v4_pre_topc @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ sk_C )
      = sk_C ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = ( k5_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ sk_C )
      = X4 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_C )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ sk_C )
      = X0 ) ),
    inference(demod,[status(thm)],['18','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v4_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['15','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('33',plain,(
    ! [X24: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X24 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X27: $i] :
      ( ~ ( v3_pre_topc @ X27 @ sk_A )
      | ~ ( v4_pre_topc @ X27 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X27 )
      | ( r2_hidden @ X27 @ sk_C )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('42',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','52'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('54',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X3: $i] :
      ( r1_tarski @ sk_C @ X3 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','58'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('63',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Rkfb65zL50
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 99 iterations in 0.028s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.46  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.46  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.46  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(t28_connsp_2, conjecture,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.46           ( ![C:$i]:
% 0.22/0.46             ( ( m1_subset_1 @
% 0.22/0.46                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.46               ( ~( ( ![D:$i]:
% 0.22/0.46                      ( ( m1_subset_1 @
% 0.22/0.46                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46                        ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.46                          ( ( v3_pre_topc @ D @ A ) & 
% 0.22/0.46                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.22/0.46                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i]:
% 0.22/0.46        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.46            ( l1_pre_topc @ A ) ) =>
% 0.22/0.46          ( ![B:$i]:
% 0.22/0.46            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.46              ( ![C:$i]:
% 0.22/0.46                ( ( m1_subset_1 @
% 0.22/0.46                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.46                  ( ~( ( ![D:$i]:
% 0.22/0.46                         ( ( m1_subset_1 @
% 0.22/0.46                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46                           ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.46                             ( ( v3_pre_topc @ D @ A ) & 
% 0.22/0.46                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.22/0.46                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.22/0.46  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t2_subset, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X12 : $i, X13 : $i]:
% 0.22/0.46         ((r2_hidden @ X12 @ X13)
% 0.22/0.46          | (v1_xboole_0 @ X13)
% 0.22/0.46          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.22/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.46  thf(t4_subset_1, axiom,
% 0.22/0.46    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.22/0.46      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.46  thf('5', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('6', plain, (![X9 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X9))),
% 0.22/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf(cc2_pre_topc, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X19 : $i, X20 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.22/0.46          | (v4_pre_topc @ X19 @ X20)
% 0.22/0.46          | ~ (v1_xboole_0 @ X19)
% 0.22/0.46          | ~ (l1_pre_topc @ X20)
% 0.22/0.46          | ~ (v2_pre_topc @ X20))),
% 0.22/0.46      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (~ (v2_pre_topc @ X0)
% 0.22/0.46          | ~ (l1_pre_topc @ X0)
% 0.22/0.46          | ~ (v1_xboole_0 @ sk_C)
% 0.22/0.46          | (v4_pre_topc @ sk_C @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.46  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.46  thf('10', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('11', plain, ((v1_xboole_0 @ sk_C)),
% 0.22/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf('12', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (~ (v2_pre_topc @ X0)
% 0.22/0.46          | ~ (l1_pre_topc @ X0)
% 0.22/0.46          | (v4_pre_topc @ sk_C @ X0))),
% 0.22/0.46      inference('demod', [status(thm)], ['8', '11'])).
% 0.22/0.46  thf('13', plain, (![X9 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X9))),
% 0.22/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf(t29_tops_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( l1_pre_topc @ A ) =>
% 0.22/0.46       ( ![B:$i]:
% 0.22/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.46           ( ( v4_pre_topc @ B @ A ) <=>
% 0.22/0.46             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.46  thf('14', plain,
% 0.22/0.46      (![X25 : $i, X26 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.22/0.46          | ~ (v4_pre_topc @ X25 @ X26)
% 0.22/0.46          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25) @ X26)
% 0.22/0.46          | ~ (l1_pre_topc @ X26))),
% 0.22/0.46      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X0) @ sk_C) @ X0)
% 0.22/0.46          | ~ (v4_pre_topc @ sk_C @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.46  thf('16', plain, (![X9 : $i]: (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X9))),
% 0.22/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf(d5_subset_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.46       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.46  thf('17', plain,
% 0.22/0.46      (![X6 : $i, X7 : $i]:
% 0.22/0.46         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.22/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.46  thf('18', plain,
% 0.22/0.46      (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.22/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.46  thf(t2_boole, axiom,
% 0.22/0.46    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.46  thf('19', plain,
% 0.22/0.46      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.46  thf('20', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('21', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('22', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ sk_C) = (sk_C))),
% 0.22/0.46      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.22/0.46  thf(t100_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.46  thf('23', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.46           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.46  thf('24', plain,
% 0.22/0.46      (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (k5_xboole_0 @ X0 @ sk_C))),
% 0.22/0.46      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.46  thf(t5_boole, axiom,
% 0.22/0.46    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.46  thf('25', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.22/0.46      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.46  thf('26', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('27', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ sk_C) = (X4))),
% 0.22/0.46      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.46  thf('28', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ sk_C) = (X0))),
% 0.22/0.46      inference('sup+', [status(thm)], ['24', '27'])).
% 0.22/0.46  thf('29', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ sk_C) = (X0))),
% 0.22/0.46      inference('demod', [status(thm)], ['18', '28'])).
% 0.22/0.46  thf('30', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.46          | ~ (v4_pre_topc @ sk_C @ X0))),
% 0.22/0.46      inference('demod', [status(thm)], ['15', '29'])).
% 0.22/0.46  thf('31', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (~ (l1_pre_topc @ X0)
% 0.22/0.46          | ~ (v2_pre_topc @ X0)
% 0.22/0.46          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.46          | ~ (l1_pre_topc @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '30'])).
% 0.22/0.46  thf('32', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.22/0.46          | ~ (v2_pre_topc @ X0)
% 0.22/0.46          | ~ (l1_pre_topc @ X0))),
% 0.22/0.46      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.46  thf(fc4_pre_topc, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.46       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.22/0.46  thf('33', plain,
% 0.22/0.46      (![X24 : $i]:
% 0.22/0.46         ((v4_pre_topc @ (k2_struct_0 @ X24) @ X24)
% 0.22/0.46          | ~ (l1_pre_topc @ X24)
% 0.22/0.46          | ~ (v2_pre_topc @ X24))),
% 0.22/0.46      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.22/0.46  thf(d3_struct_0, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.46  thf('34', plain,
% 0.22/0.46      (![X21 : $i]:
% 0.22/0.46         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.22/0.46      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.46  thf(dt_k2_subset_1, axiom,
% 0.22/0.46    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.46  thf('35', plain,
% 0.22/0.46      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.46  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.46  thf('36', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.22/0.46      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.46  thf('37', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.46      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.46  thf('38', plain,
% 0.22/0.46      (![X27 : $i]:
% 0.22/0.46         (~ (v3_pre_topc @ X27 @ sk_A)
% 0.22/0.46          | ~ (v4_pre_topc @ X27 @ sk_A)
% 0.22/0.46          | ~ (r2_hidden @ sk_B @ X27)
% 0.22/0.46          | (r2_hidden @ X27 @ sk_C)
% 0.22/0.46          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('39', plain,
% 0.22/0.46      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.22/0.46        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.22/0.46        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.46  thf('40', plain,
% 0.22/0.46      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.22/0.46        | ~ (l1_struct_0 @ sk_A)
% 0.22/0.46        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.22/0.46        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.46      inference('sup-', [status(thm)], ['34', '39'])).
% 0.22/0.46  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(dt_l1_pre_topc, axiom,
% 0.22/0.46    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.46  thf('42', plain,
% 0.22/0.46      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.46  thf('43', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.46      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.46  thf('44', plain,
% 0.22/0.46      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.22/0.46        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.22/0.46        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.46      inference('demod', [status(thm)], ['40', '43'])).
% 0.22/0.46  thf('45', plain,
% 0.22/0.46      ((~ (v2_pre_topc @ sk_A)
% 0.22/0.46        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.46        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.22/0.46        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['33', '44'])).
% 0.22/0.46  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('48', plain,
% 0.22/0.46      (((r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.22/0.46        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.22/0.46      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.22/0.46  thf('49', plain,
% 0.22/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.46        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.46        | ~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.46      inference('sup-', [status(thm)], ['32', '48'])).
% 0.22/0.46  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('52', plain,
% 0.22/0.46      ((~ (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.46      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.22/0.46  thf('53', plain,
% 0.22/0.46      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | (r2_hidden @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.22/0.46      inference('sup-', [status(thm)], ['3', '52'])).
% 0.22/0.46  thf(t7_ordinal1, axiom,
% 0.22/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.46  thf('54', plain,
% 0.22/0.46      (![X17 : $i, X18 : $i]:
% 0.22/0.46         (~ (r2_hidden @ X17 @ X18) | ~ (r1_tarski @ X18 @ X17))),
% 0.22/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.46  thf('55', plain,
% 0.22/0.46      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.46        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.46  thf('56', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.46  thf('57', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('58', plain, (![X3 : $i]: (r1_tarski @ sk_C @ X3)),
% 0.22/0.46      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.46  thf('59', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.46      inference('demod', [status(thm)], ['55', '58'])).
% 0.22/0.46  thf(fc2_struct_0, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.46       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.46  thf('60', plain,
% 0.22/0.46      (![X23 : $i]:
% 0.22/0.46         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.22/0.46          | ~ (l1_struct_0 @ X23)
% 0.22/0.46          | (v2_struct_0 @ X23))),
% 0.22/0.46      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.46  thf('61', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.46  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.46      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.46  thf('63', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.46      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.46  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
