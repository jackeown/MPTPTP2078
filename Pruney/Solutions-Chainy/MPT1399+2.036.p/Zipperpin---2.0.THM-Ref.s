%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IQXo89WE1n

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 148 expanded)
%              Number of leaves         :   36 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  597 (1440 expanded)
%              Number of equality atoms :   29 (  54 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X4: $i] :
      ( ( k1_subset_1 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ( r2_hidden @ X11 @ ( k3_subset_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_subset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r2_hidden @ X2 @ ( k3_subset_1 @ X0 @ ( k1_subset_1 @ X1 ) ) )
      | ( r2_hidden @ X2 @ ( k1_subset_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k1_subset_1 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k1_subset_1 @ X4 )
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
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = ( k3_subset_1 @ X7 @ ( k1_subset_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('12',plain,(
    ! [X7: $i] :
      ( X7
      = ( k3_subset_1 @ X7 @ ( k1_subset_1 @ X7 ) ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k1_subset_1 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('26',plain,(
    ! [X21: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('27',plain,(
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

thf('28',plain,(
    ! [X20: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('29',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('31',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('32',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X22: $i] :
      ( ~ ( v3_pre_topc @ X22 @ sk_A )
      | ~ ( v4_pre_topc @ X22 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X22 )
      | ( r2_hidden @ X22 @ sk_C )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X22: $i] :
      ( ~ ( v3_pre_topc @ X22 @ sk_A )
      | ~ ( v4_pre_topc @ X22 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X22 )
      | ( r2_hidden @ X22 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('39',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('48',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('58',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('62',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IQXo89WE1n
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 259 iterations in 0.087s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(t28_connsp_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @
% 0.21/0.54                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54               ( ~( ( ![D:$i]:
% 0.21/0.54                      ( ( m1_subset_1 @
% 0.21/0.54                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                        ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54                          ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.54                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.54                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( m1_subset_1 @
% 0.21/0.54                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54                  ( ~( ( ![D:$i]:
% 0.21/0.54                         ( ( m1_subset_1 @
% 0.21/0.54                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                           ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54                             ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.54                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.54                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.21/0.54  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('2', plain, (![X4 : $i]: ((k1_subset_1 @ X4) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.54  thf(t4_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf(t50_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.54               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.21/0.54                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.21/0.54          | (r2_hidden @ X11 @ X9)
% 0.21/0.54          | (r2_hidden @ X11 @ (k3_subset_1 @ X10 @ X9))
% 0.21/0.54          | ~ (m1_subset_1 @ X11 @ X10)
% 0.21/0.54          | ((X10) = (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t50_subset_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (((X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.54          | (r2_hidden @ X2 @ (k3_subset_1 @ X0 @ (k1_subset_1 @ X1)))
% 0.21/0.54          | (r2_hidden @ X2 @ (k1_subset_1 @ X1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain, (![X4 : $i]: ((k1_subset_1 @ X4) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.54  thf('8', plain, (![X4 : $i]: ((k1_subset_1 @ X4) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf(t22_subset_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X7 : $i]:
% 0.21/0.54         ((k2_subset_1 @ X7) = (k3_subset_1 @ X7 @ (k1_subset_1 @ X7)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.21/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.54  thf('11', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X7 : $i]: ((X7) = (k3_subset_1 @ X7 @ (k1_subset_1 @ X7)))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['9', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (((X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.54          | (r2_hidden @ X2 @ X0)
% 0.21/0.54          | (r2_hidden @ X2 @ (k1_subset_1 @ X1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['6', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ sk_B_1 @ (k1_subset_1 @ X0))
% 0.21/0.54          | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '14'])).
% 0.21/0.54  thf(d1_xboole_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.54          | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (v1_xboole_0 @ (k1_subset_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain, (![X4 : $i]: ((k1_subset_1 @ X4) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.54  thf('19', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf(t7_ordinal1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.54  thf('24', plain, (![X0 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['18', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.54        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '24'])).
% 0.21/0.54  thf(fc10_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X21 : $i]:
% 0.21/0.54         ((v3_pre_topc @ (k2_struct_0 @ X21) @ X21)
% 0.21/0.54          | ~ (l1_pre_topc @ X21)
% 0.21/0.54          | ~ (v2_pre_topc @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.21/0.54  thf(d3_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X17 : $i]:
% 0.21/0.54         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.54  thf(fc4_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X20 : $i]:
% 0.21/0.54         ((v4_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 0.21/0.54          | ~ (l1_pre_topc @ X20)
% 0.21/0.54          | ~ (v2_pre_topc @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X17 : $i]:
% 0.21/0.54         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.54  thf(dt_k2_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.54  thf('31', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.54  thf('32', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.21/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X22 : $i]:
% 0.21/0.54         (~ (v3_pre_topc @ X22 @ sk_A)
% 0.21/0.54          | ~ (v4_pre_topc @ X22 @ sk_A)
% 0.21/0.54          | ~ (r2_hidden @ sk_B_1 @ X22)
% 0.21/0.54          | (r2_hidden @ X22 @ sk_C)
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('34', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X22 : $i]:
% 0.21/0.54         (~ (v3_pre_topc @ X22 @ sk_A)
% 0.21/0.54          | ~ (v4_pre_topc @ X22 @ sk_A)
% 0.21/0.54          | ~ (r2_hidden @ sk_B_1 @ X22)
% 0.21/0.54          | (r2_hidden @ X22 @ k1_xboole_0)
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.54        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.54        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '36'])).
% 0.21/0.54  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_l1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.54        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['37', '40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['28', '41'])).
% 0.21/0.54  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '45'])).
% 0.21/0.54  thf('47', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['26', '48'])).
% 0.21/0.54  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.54        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 0.21/0.54        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '52'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.54  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.54  thf('57', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf(fc2_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (![X19 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.21/0.54          | ~ (l1_struct_0 @ X19)
% 0.21/0.54          | (v2_struct_0 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.54  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.54  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('62', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.54  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
