%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ARUY5GPwo

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 213 expanded)
%              Number of leaves         :   28 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  678 (2347 expanded)
%              Number of equality atoms :   37 ( 133 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ X18 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tops_1 @ X20 @ X21 )
      | ( r1_tarski @ X20 @ ( k2_tops_1 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v2_tops_1 @ X22 @ X23 )
      | ~ ( v3_tops_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['28'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( r1_tarski @ X20 @ ( k2_tops_1 @ X21 @ X20 ) )
      | ( v2_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t93_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v2_tops_1 @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_tops_1 @ X24 @ X25 )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ~ ( v2_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t93_tops_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('56',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['28'])).

thf('58',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['37','56','57'])).

thf('59',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['35','58'])).

thf('60',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','59'])).

thf('61',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf('62',plain,
    ( sk_B
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','60','61'])).

thf('63',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['37','56'])).

thf('65',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9ARUY5GPwo
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:36:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 88 iterations in 0.052s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.50  thf(t94_tops_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.50             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( l1_pre_topc @ A ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50              ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.50                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(l78_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.50             ( k7_subset_1 @
% 0.20/0.50               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.50               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.50          | ((k2_tops_1 @ X19 @ X18)
% 0.20/0.50              = (k7_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.20/0.50                 (k2_pre_topc @ X19 @ X18) @ (k1_tops_1 @ X19 @ X18)))
% 0.20/0.50          | ~ (l1_pre_topc @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.50            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.50  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t52_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.50             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.50               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.50          | ~ (v4_pre_topc @ X16 @ X17)
% 0.20/0.50          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.20/0.50          | ~ (l1_pre_topc @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.20/0.50          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.50           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.50         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf(d5_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X8 @ X7)
% 0.20/0.50          | (r2_hidden @ X8 @ X5)
% 0.20/0.50          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.50         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.20/0.50          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.20/0.50          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X10 : $i, X12 : $i]:
% 0.20/0.50         (((X10) = (X12))
% 0.20/0.50          | ~ (r1_tarski @ X12 @ X10)
% 0.20/0.50          | ~ (r1_tarski @ X10 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.50          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.50        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t88_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.20/0.50             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.50          | ~ (v2_tops_1 @ X20 @ X21)
% 0.20/0.50          | (r1_tarski @ X20 @ (k2_tops_1 @ X21 @ X20))
% 0.20/0.50          | ~ (l1_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t92_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.50          | (v2_tops_1 @ X22 @ X23)
% 0.20/0.50          | ~ (v3_tops_1 @ X22 @ X23)
% 0.20/0.50          | ~ (l1_pre_topc @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.50         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['28'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.50          | ~ (r1_tarski @ X20 @ (k2_tops_1 @ X21 @ X20))
% 0.20/0.50          | (v2_tops_1 @ X20 @ X21)
% 0.20/0.50          | ~ (l1_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.20/0.50         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('46', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.20/0.50      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t93_tops_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( ( v2_tops_1 @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.50             ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.50          | (v3_tops_1 @ X24 @ X25)
% 0.20/0.50          | ~ (v4_pre_topc @ X24 @ X25)
% 0.20/0.50          | ~ (v2_tops_1 @ X24 @ X25)
% 0.20/0.50          | ~ (l1_pre_topc @ X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [t93_tops_1])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A)
% 0.20/0.50        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.50        | (v3_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('52', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain, ((~ (v2_tops_1 @ sk_B @ sk_A) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['36'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['28'])).
% 0.20/0.50  thf('58', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['37', '56', '57'])).
% 0.20/0.50  thf('59', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['35', '58'])).
% 0.20/0.50  thf('60', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.50         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 0.20/0.50  thf('62', plain, (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '60', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.50         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.50      inference('split', [status(esa)], ['36'])).
% 0.20/0.50  thf('64', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['37', '56'])).
% 0.20/0.50  thf('65', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['62', '65'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
