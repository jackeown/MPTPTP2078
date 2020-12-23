%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iaOyp7oeCZ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:11 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 129 expanded)
%              Number of leaves         :   36 (  54 expanded)
%              Depth                    :   25
%              Number of atoms          :  561 (1607 expanded)
%              Number of equality atoms :   14 (  43 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

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
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
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

thf('7',plain,(
    ! [X19: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('8',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X22: $i] :
      ( ~ ( v3_pre_topc @ X22 @ sk_A )
      | ~ ( v4_pre_topc @ X22 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X22 )
      | ( r2_hidden @ X22 @ sk_C )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X22: $i] :
      ( ~ ( v3_pre_topc @ X22 @ sk_A )
      | ~ ( v4_pre_topc @ X22 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X22 )
      | ( r2_hidden @ X22 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','37'])).

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

thf('39',plain,(
    ! [X21: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( sk_B_1 @ sk_A ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','49'])).

thf('51',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('52',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iaOyp7oeCZ
% 0.12/0.35  % Computer   : n019.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 17:42:23 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 194 iterations in 0.110s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.58  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.37/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.58  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.37/0.58  thf(t28_connsp_2, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( m1_subset_1 @
% 0.37/0.58                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58               ( ~( ( ![D:$i]:
% 0.37/0.58                      ( ( m1_subset_1 @
% 0.37/0.58                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58                        ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.58                          ( ( v3_pre_topc @ D @ A ) & 
% 0.37/0.58                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.37/0.58                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.58            ( l1_pre_topc @ A ) ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.58              ( ![C:$i]:
% 0.37/0.58                ( ( m1_subset_1 @
% 0.37/0.58                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58                  ( ~( ( ![D:$i]:
% 0.37/0.58                         ( ( m1_subset_1 @
% 0.37/0.58                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58                           ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.58                             ( ( v3_pre_topc @ D @ A ) & 
% 0.37/0.58                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.37/0.58                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.37/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t6_mcart_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.58                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.37/0.58                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.37/0.58                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.37/0.58                       ( r2_hidden @ G @ B ) ) =>
% 0.37/0.58                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X11 : $i]:
% 0.37/0.58         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.37/0.58  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t2_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i]:
% 0.37/0.58         ((r2_hidden @ X4 @ X5)
% 0.37/0.58          | (v1_xboole_0 @ X5)
% 0.37/0.58          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.37/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.58  thf(fc10_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X20 : $i]:
% 0.37/0.58         ((v3_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 0.37/0.58          | ~ (l1_pre_topc @ X20)
% 0.37/0.58          | ~ (v2_pre_topc @ X20))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.37/0.58  thf(d3_struct_0, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X17 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf(fc4_pre_topc, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X19 : $i]:
% 0.37/0.58         ((v4_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.37/0.58          | ~ (l1_pre_topc @ X19)
% 0.37/0.58          | ~ (v2_pre_topc @ X19))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X17 : $i]:
% 0.37/0.58         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.37/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.58  thf(dt_k2_subset_1, axiom,
% 0.37/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.37/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.58  thf('10', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 0.37/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.58  thf('11', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.37/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X22 : $i]:
% 0.37/0.58         (~ (v3_pre_topc @ X22 @ sk_A)
% 0.37/0.58          | ~ (v4_pre_topc @ X22 @ sk_A)
% 0.37/0.58          | ~ (r2_hidden @ sk_B_2 @ X22)
% 0.37/0.58          | (r2_hidden @ X22 @ sk_C)
% 0.37/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X22 : $i]:
% 0.37/0.58         (~ (v3_pre_topc @ X22 @ sk_A)
% 0.37/0.58          | ~ (v4_pre_topc @ X22 @ sk_A)
% 0.37/0.58          | ~ (r2_hidden @ sk_B_2 @ X22)
% 0.37/0.58          | (r2_hidden @ X22 @ k1_xboole_0)
% 0.37/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['11', '14'])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['8', '15'])).
% 0.37/0.58  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(dt_l1_pre_topc, axiom,
% 0.37/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.58  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.37/0.58      inference('demod', [status(thm)], ['16', '19'])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['7', '20'])).
% 0.37/0.58  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['6', '24'])).
% 0.37/0.58  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.37/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '27'])).
% 0.37/0.58  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.37/0.58        | ~ (r2_hidden @ sk_B_2 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['4', '31'])).
% 0.37/0.58  thf(t7_ordinal1, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X9 : $i, X10 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.37/0.58        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.58  thf('35', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.37/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.58  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.58  thf(l13_xboole_0, axiom,
% 0.37/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.58  thf('38', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf(rc3_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ?[B:$i]:
% 0.37/0.58         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.37/0.58           ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.58           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X21 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (sk_B_1 @ X21) @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.58          | ~ (l1_pre_topc @ X21)
% 0.37/0.58          | ~ (v2_pre_topc @ X21)
% 0.37/0.58          | (v2_struct_0 @ X21))),
% 0.37/0.58      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      (((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.37/0.58        | (v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.58      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.58  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      (((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.37/0.58        | (v2_struct_0 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.37/0.58  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      ((m1_subset_1 @ (sk_B_1 @ sk_A) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.37/0.58      inference('clc', [status(thm)], ['43', '44'])).
% 0.37/0.58  thf(t5_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.58          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.58         (~ (r2_hidden @ X6 @ X7)
% 0.37/0.58          | ~ (v1_xboole_0 @ X8)
% 0.37/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.58  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.58  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_B_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.58  thf('50', plain, (((sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '49'])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      (![X21 : $i]:
% 0.37/0.58         (~ (v1_xboole_0 @ (sk_B_1 @ X21))
% 0.37/0.58          | ~ (l1_pre_topc @ X21)
% 0.37/0.58          | ~ (v2_pre_topc @ X21)
% 0.37/0.58          | (v2_struct_0 @ X21))),
% 0.37/0.58      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.58        | (v2_struct_0 @ sk_A)
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.58  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.58  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('56', plain, ((v2_struct_0 @ sk_A)),
% 0.37/0.58      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.37/0.58  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
