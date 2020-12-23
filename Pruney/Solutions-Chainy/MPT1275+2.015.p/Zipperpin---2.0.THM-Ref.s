%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BCnMn0WMiw

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 206 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  654 (2172 expanded)
%              Number of equality atoms :   49 ( 138 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_tops_1 @ X51 @ X50 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ X50 ) @ ( k1_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
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
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ~ ( v4_pre_topc @ X46 @ X47 )
      | ( ( k2_pre_topc @ X47 @ X46 )
        = X46 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
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

thf('10',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( v2_tops_1 @ X56 @ X57 )
      | ~ ( v3_tops_1 @ X56 @ X57 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( v2_tops_1 @ X52 @ X53 )
      | ( ( k1_tops_1 @ X53 @ X52 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('28',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( r1_tarski @ X54 @ ( k2_tops_1 @ X55 @ X54 ) )
      | ( v2_tops_1 @ X54 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('37',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X49 @ X48 ) @ X49 )
      | ( v3_tops_1 @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('41',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['24'])).

thf('44',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('46',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['25','44','45'])).

thf('47',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('51',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('54',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('55',plain,(
    ! [X39: $i] :
      ( ( k2_subset_1 @ X39 )
      = ( k3_subset_1 @ X39 @ ( k1_subset_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('56',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('57',plain,(
    ! [X39: $i] :
      ( X39
      = ( k3_subset_1 @ X39 @ ( k1_subset_1 @ X39 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['2','3','9','47','50','59'])).

thf('61',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['24'])).

thf('62',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['25','44'])).

thf('63',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BCnMn0WMiw
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 117 iterations in 0.027s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.48  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.48  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.48  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.48  thf(t94_tops_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.48             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( l1_pre_topc @ A ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48              ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.48                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(l78_tops_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.48             ( k7_subset_1 @
% 0.21/0.48               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.48               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X50 : $i, X51 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.21/0.48          | ((k2_tops_1 @ X51 @ X50)
% 0.21/0.48              = (k7_subset_1 @ (u1_struct_0 @ X51) @ 
% 0.21/0.48                 (k2_pre_topc @ X51 @ X50) @ (k1_tops_1 @ X51 @ X50)))
% 0.21/0.48          | ~ (l1_pre_topc @ X51))),
% 0.21/0.48      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.48            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.48               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t52_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.48             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.48               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X46 : $i, X47 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.21/0.48          | ~ (v4_pre_topc @ X46 @ X47)
% 0.21/0.48          | ((k2_pre_topc @ X47 @ X46) = (X46))
% 0.21/0.48          | ~ (l1_pre_topc @ X47))),
% 0.21/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.21/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t92_tops_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X56 : $i, X57 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 0.21/0.48          | (v2_tops_1 @ X56 @ X57)
% 0.21/0.48          | ~ (v3_tops_1 @ X56 @ X57)
% 0.21/0.48          | ~ (l1_pre_topc @ X57))),
% 0.21/0.48      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.21/0.48        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t84_tops_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.48             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X52 : $i, X53 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.21/0.48          | ~ (v2_tops_1 @ X52 @ X53)
% 0.21/0.48          | ((k1_tops_1 @ X53 @ X52) = (k1_xboole_0))
% 0.21/0.48          | ~ (l1_pre_topc @ X53))),
% 0.21/0.48      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.48        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.48        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.21/0.48         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.48         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['10'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t88_tops_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.48             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X54 : $i, X55 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 0.21/0.48          | ~ (r1_tarski @ X54 @ (k2_tops_1 @ X55 @ X54))
% 0.21/0.48          | (v2_tops_1 @ X54 @ X55)
% 0.21/0.48          | ~ (l1_pre_topc @ X55))),
% 0.21/0.48      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((v2_tops_1 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.21/0.48         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '31'])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('34', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.48      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d5_tops_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( v3_tops_1 @ B @ A ) <=>
% 0.21/0.48             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X48 : $i, X49 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.21/0.48          | ~ (v2_tops_1 @ (k2_pre_topc @ X49 @ X48) @ X49)
% 0.21/0.48          | (v3_tops_1 @ X48 @ X49)
% 0.21/0.48          | ~ (l1_pre_topc @ X49))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v3_tops_1 @ sk_B @ sk_A)
% 0.21/0.48        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.48  thf('41', plain, (((v3_tops_1 @ sk_B @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['24'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['10'])).
% 0.21/0.48  thf('46', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['25', '44', '45'])).
% 0.21/0.48  thf('47', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['23', '46'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.21/0.48          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.48           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf(t4_subset_1, axiom,
% 0.21/0.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.48  thf(d5_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X34 : $i, X35 : $i]:
% 0.21/0.48         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.21/0.48          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.48  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('54', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.48  thf(t22_subset_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (![X39 : $i]:
% 0.21/0.48         ((k2_subset_1 @ X39) = (k3_subset_1 @ X39 @ (k1_subset_1 @ X39)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.21/0.48  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.48  thf('56', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (![X39 : $i]: ((X39) = (k3_subset_1 @ X39 @ (k1_subset_1 @ X39)))),
% 0.21/0.48      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.48  thf('58', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['54', '57'])).
% 0.21/0.48  thf('59', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['53', '58'])).
% 0.21/0.48  thf('60', plain, (((k2_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3', '9', '47', '50', '59'])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.48         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['24'])).
% 0.21/0.48  thf('62', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['25', '44'])).
% 0.21/0.48  thf('63', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.21/0.48  thf('64', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['60', '63'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
