%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rvt4hYuirZ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:11 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 138 expanded)
%              Number of leaves         :   35 (  57 expanded)
%              Depth                    :   25
%              Number of atoms          :  578 (1672 expanded)
%              Number of equality atoms :   14 (  46 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X20: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
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

thf('7',plain,(
    ! [X18: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('8',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X21: $i] :
      ( ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( v4_pre_topc @ X21 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X21 )
      | ( r2_hidden @ X21 @ sk_C )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X21: $i] :
      ( ~ ( v3_pre_topc @ X21 @ sk_A )
      | ~ ( v4_pre_topc @ X21 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X21 )
      | ( r2_hidden @ X21 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','31'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('38',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','41'])).

thf(rc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X19: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('44',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','53'])).

thf('55',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[rc7_pre_topc])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rvt4hYuirZ
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:05:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 175 iterations in 0.192s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.65  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.65  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.65  thf(t28_connsp_2, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( m1_subset_1 @
% 0.45/0.65                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65               ( ~( ( ![D:$i]:
% 0.45/0.65                      ( ( m1_subset_1 @
% 0.45/0.65                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                        ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65                          ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.65                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.65                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.45/0.65            ( l1_pre_topc @ A ) ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.65              ( ![C:$i]:
% 0.45/0.65                ( ( m1_subset_1 @
% 0.45/0.65                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.65                  ( ~( ( ![D:$i]:
% 0.45/0.65                         ( ( m1_subset_1 @
% 0.45/0.65                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.65                           ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65                             ( ( v3_pre_topc @ D @ A ) & 
% 0.45/0.65                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.45/0.65                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.45/0.65  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t6_mcart_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.65                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.65                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.45/0.65                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.45/0.65                       ( r2_hidden @ G @ B ) ) =>
% 0.45/0.65                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X10 : $i]:
% 0.45/0.65         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.45/0.65  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t2_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.65       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]:
% 0.45/0.65         ((r2_hidden @ X3 @ X4)
% 0.45/0.65          | (v1_xboole_0 @ X4)
% 0.45/0.65          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(fc10_tops_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X20 : $i]:
% 0.45/0.65         ((v3_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 0.45/0.65          | ~ (l1_pre_topc @ X20)
% 0.45/0.65          | ~ (v2_pre_topc @ X20))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.45/0.65  thf(d3_struct_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X16 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf(fc4_pre_topc, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X18 : $i]:
% 0.45/0.65         ((v4_pre_topc @ (k2_struct_0 @ X18) @ X18)
% 0.45/0.65          | ~ (l1_pre_topc @ X18)
% 0.45/0.65          | ~ (v2_pre_topc @ X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X16 : $i]:
% 0.45/0.65         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.65  thf(dt_k2_subset_1, axiom,
% 0.45/0.65    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.45/0.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.45/0.65  thf('10', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.45/0.65  thf('11', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X21 : $i]:
% 0.45/0.65         (~ (v3_pre_topc @ X21 @ sk_A)
% 0.45/0.65          | ~ (v4_pre_topc @ X21 @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ sk_B_2 @ X21)
% 0.45/0.65          | (r2_hidden @ X21 @ sk_C)
% 0.45/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X21 : $i]:
% 0.45/0.65         (~ (v3_pre_topc @ X21 @ sk_A)
% 0.45/0.65          | ~ (v4_pre_topc @ X21 @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ sk_B_2 @ X21)
% 0.45/0.65          | (r2_hidden @ X21 @ k1_xboole_0)
% 0.45/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['11', '14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['8', '15'])).
% 0.45/0.65  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_l1_pre_topc, axiom,
% 0.45/0.65    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.65  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['16', '19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '20'])).
% 0.45/0.65  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['6', '24'])).
% 0.45/0.65  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      ((~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '27'])).
% 0.45/0.65  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.45/0.65        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '31'])).
% 0.45/0.65  thf(t7_ordinal1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.45/0.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.65        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.65  thf('35', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.65  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X10 : $i]:
% 0.45/0.65         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.45/0.65  thf('38', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.45/0.65      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.65  thf(t5_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.65          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X5 @ X6)
% 0.45/0.65          | ~ (v1_xboole_0 @ X7)
% 0.45/0.65          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '40'])).
% 0.45/0.65  thf('42', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['36', '41'])).
% 0.45/0.65  thf(rc7_pre_topc, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.65       ( ?[B:$i]:
% 0.45/0.65         ( ( v4_pre_topc @ B @ A ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.45/0.65           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X19 : $i]:
% 0.45/0.65         ((m1_subset_1 @ (sk_B_1 @ X19) @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.65          | ~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup+', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.45/0.65        | (v2_struct_0 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.45/0.65  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      ((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('clc', [status(thm)], ['47', '48'])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X5 @ X6)
% 0.45/0.65          | ~ (v1_xboole_0 @ X7)
% 0.45/0.65          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.65  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.65  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))),
% 0.45/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('54', plain, (((sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '53'])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      (![X19 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ (sk_B_1 @ X19))
% 0.45/0.65          | ~ (l1_pre_topc @ X19)
% 0.45/0.65          | ~ (v2_pre_topc @ X19)
% 0.45/0.65          | (v2_struct_0 @ X19))),
% 0.45/0.65      inference('cnf', [status(esa)], [rc7_pre_topc])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.65        | (v2_struct_0 @ sk_A)
% 0.45/0.65        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.65  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('60', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.65      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.45/0.65  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
