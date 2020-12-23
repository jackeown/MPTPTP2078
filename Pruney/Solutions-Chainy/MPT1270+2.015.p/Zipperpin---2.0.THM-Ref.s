%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rCVpyms788

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 147 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  781 (1462 expanded)
%              Number of equality atoms :   38 (  47 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('5',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ~ ( v2_tops_1 @ X57 @ X58 )
      | ( ( k1_tops_1 @ X58 @ X57 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_tops_1 @ X54 @ X53 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X54 ) @ ( k2_pre_topc @ X54 @ X53 ) @ ( k1_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X49 @ X50 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','20'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( r1_tarski @ X51 @ ( k2_pre_topc @ X52 @ X51 ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k1_tops_1 @ X56 @ X55 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','40'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k4_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('54',plain,
    ( ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['46'])).

thf('57',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k1_tops_1 @ X58 @ X57 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X57 @ X58 )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rCVpyms788
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 228 iterations in 0.130s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(t88_tops_1, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.58             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( l1_pre_topc @ A ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58              ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.58                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.58        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.21/0.58       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.58        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t84_tops_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.58             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X57 : $i, X58 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.21/0.58          | ~ (v2_tops_1 @ X57 @ X58)
% 0.21/0.58          | ((k1_tops_1 @ X58 @ X57) = (k1_xboole_0))
% 0.21/0.58          | ~ (l1_pre_topc @ X58))),
% 0.21/0.58      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.58        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.58        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.58         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(l78_tops_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.58             ( k7_subset_1 @
% 0.21/0.58               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.58               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X53 : $i, X54 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 0.21/0.58          | ((k2_tops_1 @ X54 @ X53)
% 0.21/0.58              = (k7_subset_1 @ (u1_struct_0 @ X54) @ 
% 0.21/0.58                 (k2_pre_topc @ X54 @ X53) @ (k1_tops_1 @ X54 @ X53)))
% 0.21/0.58          | ~ (l1_pre_topc @ X54))),
% 0.21/0.58      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.58               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_k2_pre_topc, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58       ( m1_subset_1 @
% 0.21/0.58         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X49 : $i, X50 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X49)
% 0.21/0.58          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.21/0.58          | (m1_subset_1 @ (k2_pre_topc @ X49 @ X50) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X49))))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.58  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.21/0.58          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.58           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['12', '13', '20'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ k1_xboole_0)))
% 0.21/0.58         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '21'])).
% 0.21/0.58  thf(t3_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('23', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.58         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t48_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X51 : $i, X52 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 0.21/0.58          | (r1_tarski @ X51 @ (k2_pre_topc @ X52 @ X51))
% 0.21/0.58          | ~ (l1_pre_topc @ X52))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.58  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('29', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['24', '29'])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.21/0.58       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.21/0.58       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t74_tops_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.58             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X55 : $i, X56 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.21/0.58          | ((k1_tops_1 @ X56 @ X55)
% 0.21/0.58              = (k7_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 0.21/0.58                 (k2_tops_1 @ X56 @ X55)))
% 0.21/0.58          | ~ (l1_pre_topc @ X56))),
% 0.21/0.58      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 0.21/0.58          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.58         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['36', '37', '40'])).
% 0.21/0.58  thf(d5_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.58       ( ![D:$i]:
% 0.21/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.58           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.58         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.21/0.58          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.21/0.58          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.58  thf('43', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.58          | ~ (r2_hidden @ X8 @ X6)
% 0.21/0.58          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.58          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.58  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.58      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.58          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['42', '47'])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf(d3_tarski, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.58          | (r2_hidden @ X0 @ X2)
% 0.21/0.58          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          ((r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.58           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      ((![X0 : $i]:
% 0.21/0.58          (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ X0))
% 0.21/0.58           | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_B) @ 
% 0.21/0.58              (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.58         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.21/0.58          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.21/0.58          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58         | (r2_hidden @ 
% 0.21/0.58            (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.58            k1_xboole_0)
% 0.21/0.58         | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      ((((r2_hidden @ 
% 0.21/0.58          (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ k1_xboole_0)
% 0.21/0.58         | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.58  thf('56', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.58      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      ((((k1_xboole_0) = (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['41', '57'])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (![X57 : $i, X58 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 0.21/0.58          | ((k1_tops_1 @ X58 @ X57) != (k1_xboole_0))
% 0.21/0.58          | (v2_tops_1 @ X57 @ X58)
% 0.21/0.58          | ~ (l1_pre_topc @ X58))),
% 0.21/0.58      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | (v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.58        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.58  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (((v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.58        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['58', '63'])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      (((v2_tops_1 @ sk_B @ sk_A))
% 0.21/0.58         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.21/0.58       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.58  thf('68', plain, ($false),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['1', '32', '33', '67'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
