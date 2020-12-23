%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.51gQfHD2pz

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:10 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 203 expanded)
%              Number of leaves         :   35 (  75 expanded)
%              Depth                    :   22
%              Number of atoms          :  572 (2611 expanded)
%              Number of equality atoms :   21 (  77 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X15 ) @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('6',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('7',plain,(
    ! [X14: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf('8',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('11',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i] :
      ( ~ ( v3_pre_topc @ X18 @ sk_A )
      | ~ ( v4_pre_topc @ X18 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X18 )
      | ( r2_hidden @ X18 @ sk_C )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X18: $i] :
      ( ~ ( v3_pre_topc @ X18 @ sk_A )
      | ~ ( v4_pre_topc @ X18 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X18 )
      | ( r2_hidden @ X18 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
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
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
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
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
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

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('41',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf(fc14_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ~ ( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('42',plain,(
    ! [X17: $i] :
      ( ~ ( v2_tops_1 @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc14_tops_1])).

thf('43',plain,
    ( ~ ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(rc5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ? [B: $i] :
          ( ( v2_tops_1 @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('48',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc5_tops_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('52',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X16: $i] :
      ( ( v2_tops_1 @ ( sk_B @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc5_tops_1])).

thf('59',plain,
    ( ( v2_tops_1 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_tops_1 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['46','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['0','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.51gQfHD2pz
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:34:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 176 iterations in 0.141s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.57  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.36/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
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
% 0.36/0.58  thf(d3_struct_0, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X12 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t2_subset, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.58       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X5 : $i, X6 : $i]:
% 0.36/0.58         ((r2_hidden @ X5 @ X6)
% 0.36/0.58          | (v1_xboole_0 @ X6)
% 0.36/0.58          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.36/0.58      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf(fc10_tops_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X15 : $i]:
% 0.36/0.58         ((v3_pre_topc @ (k2_struct_0 @ X15) @ X15)
% 0.36/0.58          | ~ (l1_pre_topc @ X15)
% 0.36/0.58          | ~ (v2_pre_topc @ X15))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X12 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf(fc4_pre_topc, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X14 : $i]:
% 0.36/0.58         ((v4_pre_topc @ (k2_struct_0 @ X14) @ X14)
% 0.36/0.58          | ~ (l1_pre_topc @ X14)
% 0.36/0.58          | ~ (v2_pre_topc @ X14))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (![X12 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf(dt_k2_subset_1, axiom,
% 0.36/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.36/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.58  thf('10', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.58  thf('11', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.36/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (~ (v3_pre_topc @ X18 @ sk_A)
% 0.36/0.58          | ~ (v4_pre_topc @ X18 @ sk_A)
% 0.36/0.58          | ~ (r2_hidden @ sk_B_1 @ X18)
% 0.36/0.58          | (r2_hidden @ X18 @ sk_C)
% 0.36/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (~ (v3_pre_topc @ X18 @ sk_A)
% 0.36/0.58          | ~ (v4_pre_topc @ X18 @ sk_A)
% 0.36/0.58          | ~ (r2_hidden @ sk_B_1 @ X18)
% 0.36/0.58          | (r2_hidden @ X18 @ k1_xboole_0)
% 0.36/0.58          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | ~ (v4_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['11', '14'])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['8', '15'])).
% 0.36/0.58  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(dt_l1_pre_topc, axiom,
% 0.36/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.36/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.58  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      ((~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['16', '19'])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['7', '20'])).
% 0.36/0.58  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['6', '24'])).
% 0.36/0.58  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      ((~ (v2_pre_topc @ sk_A)
% 0.36/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['5', '27'])).
% 0.36/0.58  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (((r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.36/0.58        | ~ (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | (r2_hidden @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '31'])).
% 0.36/0.58  thf(t7_ordinal1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X10 : $i, X11 : $i]:
% 0.36/0.58         (~ (r2_hidden @ X10 @ X11) | ~ (r1_tarski @ X11 @ X10))),
% 0.36/0.58      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.58        | ~ (r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.58  thf('35', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.36/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.58  thf('36', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.58  thf(l13_xboole_0, axiom,
% 0.36/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.58  thf('38', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.58      inference('sup+', [status(thm)], ['1', '38'])).
% 0.36/0.58  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.58  thf('41', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.58  thf(fc14_tops_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( ~( v2_tops_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X17 : $i]:
% 0.36/0.58         (~ (v2_tops_1 @ (k2_struct_0 @ X17) @ X17)
% 0.36/0.58          | ~ (l1_pre_topc @ X17)
% 0.36/0.58          | ~ (v2_pre_topc @ X17)
% 0.36/0.58          | (v2_struct_0 @ X17))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc14_tops_1])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      ((~ (v2_tops_1 @ k1_xboole_0 @ sk_A)
% 0.36/0.58        | (v2_struct_0 @ sk_A)
% 0.36/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.58  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      ((~ (v2_tops_1 @ k1_xboole_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.36/0.58  thf('47', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.36/0.58  thf(rc5_tops_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_pre_topc @ A ) =>
% 0.36/0.58       ( ?[B:$i]:
% 0.36/0.58         ( ( v2_tops_1 @ B @ A ) & 
% 0.36/0.58           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      (![X16 : $i]:
% 0.36/0.58         ((m1_subset_1 @ (sk_B @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.58          | ~ (l1_pre_topc @ X16))),
% 0.36/0.58      inference('cnf', [status(esa)], [rc5_tops_1])).
% 0.36/0.58  thf(t3_subset, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (![X7 : $i, X8 : $i]:
% 0.36/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (l1_pre_topc @ X0) | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.58  thf(t3_xboole_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.58  thf('52', plain,
% 0.36/0.58      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.36/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.36/0.58  thf('53', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (~ (r1_tarski @ X1 @ X0)
% 0.36/0.58          | ~ (v1_xboole_0 @ X0)
% 0.36/0.58          | ((X1) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.58  thf('54', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (l1_pre_topc @ X0)
% 0.36/0.58          | ((sk_B @ X0) = (k1_xboole_0))
% 0.36/0.58          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['50', '53'])).
% 0.36/0.58  thf('55', plain,
% 0.36/0.58      ((((sk_B @ sk_A) = (k1_xboole_0)) | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['47', '54'])).
% 0.36/0.58  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('57', plain, (((sk_B @ sk_A) = (k1_xboole_0))),
% 0.36/0.58      inference('demod', [status(thm)], ['55', '56'])).
% 0.36/0.58  thf('58', plain,
% 0.36/0.58      (![X16 : $i]: ((v2_tops_1 @ (sk_B @ X16) @ X16) | ~ (l1_pre_topc @ X16))),
% 0.36/0.58      inference('cnf', [status(esa)], [rc5_tops_1])).
% 0.36/0.58  thf('59', plain,
% 0.36/0.58      (((v2_tops_1 @ k1_xboole_0 @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.58      inference('sup+', [status(thm)], ['57', '58'])).
% 0.36/0.58  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('61', plain, ((v2_tops_1 @ k1_xboole_0 @ sk_A)),
% 0.36/0.58      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.58  thf('62', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.58      inference('demod', [status(thm)], ['46', '61'])).
% 0.36/0.58  thf('63', plain, ($false), inference('demod', [status(thm)], ['0', '62'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
