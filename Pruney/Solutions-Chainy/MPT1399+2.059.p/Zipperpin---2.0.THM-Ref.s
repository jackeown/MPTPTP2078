%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tQXVwN0Uwe

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:10 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 202 expanded)
%              Number of leaves         :   37 (  76 expanded)
%              Depth                    :   22
%              Number of atoms          :  580 (2614 expanded)
%              Number of equality atoms :   17 (  72 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('4',plain,(
    ! [X20: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X19: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('7',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X23: $i] :
      ( ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( v4_pre_topc @ X23 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X23 )
      | ( r2_hidden @ X23 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X23: $i] :
      ( ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( v4_pre_topc @ X23 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X23 )
      | ( r2_hidden @ X23 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('26',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','30'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('40',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf(fc14_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ~ ( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('41',plain,(
    ! [X22: $i] :
      ( ~ ( v2_tops_1 @ ( k2_struct_0 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc14_tops_1])).

thf('42',plain,
    ( ~ ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ~ ( v2_tops_1 @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('49',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(rc5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v2_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc5_tops_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X21: $i] :
      ( ( v2_tops_1 @ ( sk_B_1 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc5_tops_1])).

thf('58',plain,
    ( ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_tops_1 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['47','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tQXVwN0Uwe
% 0.12/0.35  % Computer   : n019.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 13:54:07 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 162 iterations in 0.126s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.60  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.42/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.42/0.60  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.42/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.42/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.60  thf(d3_struct_0, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (![X17 : $i]:
% 0.42/0.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.60  thf(t28_connsp_2, conjecture,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60           ( ![C:$i]:
% 0.42/0.60             ( ( m1_subset_1 @
% 0.42/0.60                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.60               ( ~( ( ![D:$i]:
% 0.42/0.60                      ( ( m1_subset_1 @
% 0.42/0.60                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.60                        ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.60                          ( ( v3_pre_topc @ D @ A ) & 
% 0.42/0.60                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.42/0.60                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]:
% 0.42/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.60            ( l1_pre_topc @ A ) ) =>
% 0.42/0.60          ( ![B:$i]:
% 0.42/0.60            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.60              ( ![C:$i]:
% 0.42/0.60                ( ( m1_subset_1 @
% 0.42/0.60                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.60                  ( ~( ( ![D:$i]:
% 0.42/0.60                         ( ( m1_subset_1 @
% 0.42/0.60                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.60                           ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.60                             ( ( v3_pre_topc @ D @ A ) & 
% 0.42/0.60                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.42/0.60                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.42/0.60  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t2_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ A @ B ) =>
% 0.42/0.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i]:
% 0.42/0.60         ((r2_hidden @ X4 @ X5)
% 0.42/0.60          | (v1_xboole_0 @ X5)
% 0.42/0.60          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.42/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf(fc10_tops_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.60       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X20 : $i]:
% 0.42/0.60         ((v3_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 0.42/0.60          | ~ (l1_pre_topc @ X20)
% 0.42/0.60          | ~ (v2_pre_topc @ X20))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X17 : $i]:
% 0.42/0.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.60  thf(fc4_pre_topc, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.60       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X19 : $i]:
% 0.42/0.60         ((v4_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.42/0.60          | ~ (l1_pre_topc @ X19)
% 0.42/0.60          | ~ (v2_pre_topc @ X19))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X17 : $i]:
% 0.42/0.60         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.42/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.42/0.60  thf(dt_k2_subset_1, axiom,
% 0.42/0.60    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.42/0.60  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.42/0.60  thf('9', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.42/0.60  thf('10', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.42/0.60      inference('demod', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X23 : $i]:
% 0.42/0.60         (~ (v3_pre_topc @ X23 @ sk_A)
% 0.42/0.60          | ~ (v4_pre_topc @ X23 @ sk_A)
% 0.42/0.60          | ~ (r2_hidden @ sk_B_2 @ X23)
% 0.42/0.60          | (r2_hidden @ X23 @ sk_C)
% 0.42/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('12', plain, (((sk_C) = (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X23 : $i]:
% 0.42/0.60         (~ (v3_pre_topc @ X23 @ sk_A)
% 0.42/0.60          | ~ (v4_pre_topc @ X23 @ sk_A)
% 0.42/0.60          | ~ (r2_hidden @ sk_B_2 @ X23)
% 0.42/0.60          | (r2_hidden @ X23 @ k1_xboole_0)
% 0.42/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.60      inference('demod', [status(thm)], ['11', '12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.42/0.60        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['10', '13'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.42/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.42/0.60        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '14'])).
% 0.42/0.60  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(dt_l1_pre_topc, axiom,
% 0.42/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.60  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.42/0.60        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['15', '18'])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.42/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.60        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '19'])).
% 0.42/0.60  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('23', plain,
% 0.42/0.60      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.42/0.60        | ~ (l1_struct_0 @ sk_A)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['5', '23'])).
% 0.42/0.60  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.42/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.60        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '26'])).
% 0.42/0.60  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.42/0.60        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.60      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['3', '30'])).
% 0.42/0.60  thf(t7_ordinal1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.42/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.42/0.60        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.60  thf('34', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.42/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.60  thf('35', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.60  thf(l13_xboole_0, axiom,
% 0.42/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.42/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.60  thf('37', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.42/0.60      inference('sup+', [status(thm)], ['0', '37'])).
% 0.42/0.60  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.60  thf('40', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('demod', [status(thm)], ['38', '39'])).
% 0.42/0.60  thf(fc14_tops_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.60       ( ~( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      (![X22 : $i]:
% 0.42/0.60         (~ (v2_tops_1 @ (k2_struct_0 @ X22) @ X22)
% 0.42/0.60          | ~ (l1_pre_topc @ X22)
% 0.42/0.60          | ~ (v2_pre_topc @ X22)
% 0.42/0.60          | (v2_struct_0 @ X22))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc14_tops_1])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      ((~ (v2_tops_1 @ k1_xboole_0 @ sk_A)
% 0.42/0.60        | (v2_struct_0 @ sk_A)
% 0.42/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.42/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.42/0.60  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('45', plain,
% 0.42/0.60      ((~ (v2_tops_1 @ k1_xboole_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.42/0.60  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('47', plain, (~ (v2_tops_1 @ k1_xboole_0 @ sk_A)),
% 0.42/0.60      inference('clc', [status(thm)], ['45', '46'])).
% 0.42/0.60  thf(t6_mcart_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.60          ( ![B:$i]:
% 0.42/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.42/0.60                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.42/0.60                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.42/0.60                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.42/0.60                       ( r2_hidden @ G @ B ) ) =>
% 0.42/0.60                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.42/0.60  thf('48', plain,
% 0.42/0.60      (![X11 : $i]:
% 0.42/0.60         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.42/0.60      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.42/0.60  thf('49', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.60  thf(rc5_tops_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_pre_topc @ A ) =>
% 0.42/0.60       ( ?[B:$i]:
% 0.42/0.60         ( ( v2_tops_1 @ B @ A ) & 
% 0.42/0.60           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.42/0.60  thf('50', plain,
% 0.42/0.60      (![X21 : $i]:
% 0.42/0.60         ((m1_subset_1 @ (sk_B_1 @ X21) @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.60          | ~ (l1_pre_topc @ X21))),
% 0.42/0.60      inference('cnf', [status(esa)], [rc5_tops_1])).
% 0.42/0.60  thf(t5_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.42/0.60          ( v1_xboole_0 @ C ) ) ))).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X6 @ X7)
% 0.42/0.60          | ~ (v1_xboole_0 @ X8)
% 0.42/0.60          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t5_subset])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (l1_pre_topc @ X0)
% 0.42/0.60          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.42/0.60          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['49', '52'])).
% 0.42/0.60  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('55', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['53', '54'])).
% 0.42/0.60  thf('56', plain, (((sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['48', '55'])).
% 0.42/0.60  thf('57', plain,
% 0.42/0.60      (![X21 : $i]:
% 0.42/0.60         ((v2_tops_1 @ (sk_B_1 @ X21) @ X21) | ~ (l1_pre_topc @ X21))),
% 0.42/0.60      inference('cnf', [status(esa)], [rc5_tops_1])).
% 0.42/0.60  thf('58', plain,
% 0.42/0.60      (((v2_tops_1 @ k1_xboole_0 @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.42/0.60      inference('sup+', [status(thm)], ['56', '57'])).
% 0.42/0.60  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('60', plain, ((v2_tops_1 @ k1_xboole_0 @ sk_A)),
% 0.42/0.60      inference('demod', [status(thm)], ['58', '59'])).
% 0.42/0.60  thf('61', plain, ($false), inference('demod', [status(thm)], ['47', '60'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
