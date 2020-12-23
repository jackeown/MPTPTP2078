%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BRkaVM9bzd

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:14 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  229 (1910 expanded)
%              Number of leaves         :   35 ( 574 expanded)
%              Depth                    :   29
%              Number of atoms          : 1952 (17934 expanded)
%              Number of equality atoms :  137 (1197 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t84_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( ( k1_tops_1 @ A @ B )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tops_1])).

thf('0',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( v2_tops_1 @ X54 @ X55 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 ) @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('14',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X47: $i] :
      ( ( l1_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','27'])).

thf('29',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('34',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( v1_tops_1 @ X52 @ X53 )
      | ( ( k2_pre_topc @ X53 @ X52 )
        = ( k2_struct_0 @ X53 ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( l1_pre_topc @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X45 @ X46 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('49',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('50',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('54',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X36 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

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
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t27_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X56: $i] :
      ( ( ( k2_pre_topc @ X56 @ ( k2_struct_0 @ X56 ) )
        = ( k2_struct_0 @ X56 ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('62',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( r1_tarski @ X48 @ ( k2_pre_topc @ X49 @ X48 ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('63',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('70',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('72',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['54','59','70','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['51','72'])).

thf('74',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('75',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('76',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('77',plain,(
    ! [X41: $i] :
      ( ( k2_subset_1 @ X41 )
      = ( k3_subset_1 @ X41 @ ( k1_subset_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('78',plain,(
    ! [X33: $i] :
      ( ( k2_subset_1 @ X33 )
      = X33 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('79',plain,(
    ! [X41: $i] :
      ( X41
      = ( k3_subset_1 @ X41 @ ( k1_subset_1 @ X41 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['2','81'])).

thf('83',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('84',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('85',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X40 @ ( k3_subset_1 @ X40 @ X39 ) )
        = X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('90',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','95'])).

thf('97',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['83','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('99',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['82','97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('101',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k1_tops_1 @ X51 @ X50 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('105',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['99','105'])).

thf('107',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('109',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('111',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('116',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('118',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( v1_tops_1 @ X52 @ X53 )
      | ( ( k2_pre_topc @ X53 @ X52 )
        = ( k2_struct_0 @ X53 ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X56: $i] :
      ( ( ( k2_pre_topc @ X56 @ ( k2_struct_0 @ X56 ) )
        = ( k2_struct_0 @ X56 ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t27_tops_1])).

thf('121',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('123',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k2_pre_topc @ X53 @ X52 )
       != ( k2_struct_0 @ X53 ) )
      | ( v1_tops_1 @ X52 @ X53 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X47: $i] :
      ( ( l1_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['119','129'])).

thf('131',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('132',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( r1_tarski @ X48 @ ( k2_pre_topc @ X49 @ X48 ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','135'])).

thf('137',plain,(
    ! [X47: $i] :
      ( ( l1_struct_0 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['88','95'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X44: $i] :
      ( ( ( k2_struct_0 @ X44 )
        = ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('145',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('146',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('147',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('149',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('150',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','150'])).

thf('152',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('153',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('154',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','154'])).

thf('156',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['144','155'])).

thf('157',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('158',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('160',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['143','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('163',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['142','163'])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('168',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_subset_1 @ X40 @ ( k3_subset_1 @ X40 @ X39 ) )
        = X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('169',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('171',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['166','171'])).

thf('173',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('174',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('175',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('177',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k2_pre_topc @ X53 @ X52 )
       != ( k2_struct_0 @ X53 ) )
      | ( v1_tops_1 @ X52 @ X53 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('178',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 ) @ X55 )
      | ( v2_tops_1 @ X54 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('185',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('188',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['182','188'])).

thf('190',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('191',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','114','115','191'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BRkaVM9bzd
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 19:32:27 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 990 iterations in 0.316s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.54/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.76  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.54/0.76  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.54/0.76  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.54/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.76  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.54/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.54/0.76  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.54/0.76  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.54/0.76  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.54/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.54/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(t84_tops_1, conjecture,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( l1_pre_topc @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76           ( ( v2_tops_1 @ B @ A ) <=>
% 0.54/0.76             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i]:
% 0.54/0.76        ( ( l1_pre_topc @ A ) =>
% 0.54/0.76          ( ![B:$i]:
% 0.54/0.76            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76              ( ( v2_tops_1 @ B @ A ) <=>
% 0.54/0.76                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.54/0.76        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('1', plain,
% 0.54/0.76      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.54/0.76       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf(d3_struct_0, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      (![X44 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('4', plain,
% 0.54/0.76      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('split', [status(esa)], ['3'])).
% 0.54/0.76  thf('5', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(d4_tops_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( l1_pre_topc @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76           ( ( v2_tops_1 @ B @ A ) <=>
% 0.54/0.76             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.54/0.76  thf('6', plain,
% 0.54/0.76      (![X54 : $i, X55 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 0.54/0.76          | ~ (v2_tops_1 @ X54 @ X55)
% 0.54/0.76          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X55) @ X54) @ X55)
% 0.54/0.76          | ~ (l1_pre_topc @ X55))),
% 0.54/0.76      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.54/0.76  thf('7', plain,
% 0.54/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.76        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.54/0.76        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.76  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('9', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(d5_subset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.76       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.54/0.76  thf('10', plain,
% 0.54/0.76      (![X34 : $i, X35 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.76  thf('12', plain,
% 0.54/0.76      (![X44 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.76  thf('13', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.54/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.76      inference('sup+', [status(thm)], ['12', '13'])).
% 0.54/0.76  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(dt_l1_pre_topc, axiom,
% 0.54/0.76    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      (![X47 : $i]: ((l1_struct_0 @ X47) | ~ (l1_pre_topc @ X47))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.54/0.76  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('demod', [status(thm)], ['14', '17'])).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('demod', [status(thm)], ['11', '18'])).
% 0.54/0.76  thf('20', plain,
% 0.54/0.76      (![X44 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.76  thf('21', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.54/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.76      inference('sup+', [status(thm)], ['20', '21'])).
% 0.54/0.76  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.76  thf('25', plain,
% 0.54/0.76      (![X34 : $i, X35 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.54/0.76  thf('26', plain,
% 0.54/0.76      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.76  thf('27', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('demod', [status(thm)], ['19', '26'])).
% 0.54/0.76  thf('28', plain,
% 0.54/0.76      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.54/0.76        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['7', '8', '27'])).
% 0.54/0.76  thf('29', plain,
% 0.54/0.76      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['4', '28'])).
% 0.54/0.76  thf('30', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(dt_k3_subset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.76       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.54/0.76  thf('31', plain,
% 0.54/0.76      (![X37 : $i, X38 : $i]:
% 0.54/0.76         ((m1_subset_1 @ (k3_subset_1 @ X37 @ X38) @ (k1_zfmisc_1 @ X37))
% 0.54/0.76          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.54/0.76  thf('32', plain,
% 0.54/0.76      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.76  thf('33', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('demod', [status(thm)], ['19', '26'])).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.54/0.76  thf(d3_tops_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( l1_pre_topc @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76           ( ( v1_tops_1 @ B @ A ) <=>
% 0.54/0.76             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.54/0.76  thf('35', plain,
% 0.54/0.76      (![X52 : $i, X53 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.54/0.76          | ~ (v1_tops_1 @ X52 @ X53)
% 0.54/0.76          | ((k2_pre_topc @ X53 @ X52) = (k2_struct_0 @ X53))
% 0.54/0.76          | ~ (l1_pre_topc @ X53))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.54/0.76  thf('36', plain,
% 0.54/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.76        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.54/0.76            = (k2_struct_0 @ sk_A))
% 0.54/0.76        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['34', '35'])).
% 0.54/0.76  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.54/0.76          = (k2_struct_0 @ sk_A))
% 0.54/0.76        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['36', '37'])).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.54/0.76          = (k2_struct_0 @ sk_A)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['29', '38'])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.54/0.76  thf(dt_k2_pre_topc, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( l1_pre_topc @ A ) & 
% 0.54/0.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.54/0.76       ( m1_subset_1 @
% 0.54/0.76         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.54/0.76  thf('41', plain,
% 0.54/0.76      (![X45 : $i, X46 : $i]:
% 0.54/0.76         (~ (l1_pre_topc @ X45)
% 0.54/0.76          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.54/0.76          | (m1_subset_1 @ (k2_pre_topc @ X45 @ X46) @ 
% 0.54/0.76             (k1_zfmisc_1 @ (u1_struct_0 @ X45))))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.54/0.76  thf('42', plain,
% 0.54/0.76      (((m1_subset_1 @ 
% 0.54/0.76         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.54/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.54/0.76        | ~ (l1_pre_topc @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['40', '41'])).
% 0.54/0.76  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      ((m1_subset_1 @ 
% 0.54/0.76        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.76  thf('45', plain,
% 0.54/0.76      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['39', '44'])).
% 0.54/0.76  thf('46', plain,
% 0.54/0.76      (![X37 : $i, X38 : $i]:
% 0.54/0.76         ((m1_subset_1 @ (k3_subset_1 @ X37 @ X38) @ (k1_zfmisc_1 @ X37))
% 0.54/0.76          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      (((m1_subset_1 @ 
% 0.54/0.76         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) @ 
% 0.54/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['45', '46'])).
% 0.54/0.76  thf('48', plain,
% 0.54/0.76      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['39', '44'])).
% 0.54/0.76  thf('49', plain,
% 0.54/0.76      (![X34 : $i, X35 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.54/0.76  thf('50', plain,
% 0.54/0.76      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.54/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      (((m1_subset_1 @ 
% 0.54/0.76         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) @ 
% 0.54/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['47', '50'])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      (![X44 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.76  thf('53', plain,
% 0.54/0.76      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.54/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.54/0.76           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.54/0.76         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['52', '53'])).
% 0.54/0.76  thf(dt_k2_subset_1, axiom,
% 0.54/0.76    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.54/0.76  thf('55', plain,
% 0.54/0.76      (![X36 : $i]: (m1_subset_1 @ (k2_subset_1 @ X36) @ (k1_zfmisc_1 @ X36))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.54/0.76  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.54/0.76  thf('56', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.54/0.76      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.54/0.76  thf('57', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.54/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.54/0.76  thf('58', plain,
% 0.54/0.76      (![X34 : $i, X35 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.54/0.76  thf('59', plain,
% 0.54/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['57', '58'])).
% 0.54/0.76  thf(t27_tops_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( l1_pre_topc @ A ) =>
% 0.54/0.76       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.54/0.76  thf('60', plain,
% 0.54/0.76      (![X56 : $i]:
% 0.54/0.76         (((k2_pre_topc @ X56 @ (k2_struct_0 @ X56)) = (k2_struct_0 @ X56))
% 0.54/0.76          | ~ (l1_pre_topc @ X56))),
% 0.54/0.76      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.54/0.76  thf('61', plain,
% 0.54/0.76      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['39', '44'])).
% 0.54/0.76  thf(t48_pre_topc, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( l1_pre_topc @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.54/0.76  thf('62', plain,
% 0.54/0.76      (![X48 : $i, X49 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.54/0.76          | (r1_tarski @ X48 @ (k2_pre_topc @ X49 @ X48))
% 0.54/0.76          | ~ (l1_pre_topc @ X49))),
% 0.54/0.76      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.54/0.76  thf('63', plain,
% 0.54/0.76      (((~ (l1_pre_topc @ sk_A)
% 0.54/0.76         | (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.76            (k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['61', '62'])).
% 0.54/0.76  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('65', plain,
% 0.54/0.76      (((r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.76         (k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['63', '64'])).
% 0.54/0.76  thf('66', plain,
% 0.54/0.76      ((((r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.54/0.76         | ~ (l1_pre_topc @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['60', '65'])).
% 0.54/0.76  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('68', plain,
% 0.54/0.76      (((r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['66', '67'])).
% 0.54/0.76  thf(l32_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.76  thf('69', plain,
% 0.54/0.76      (![X0 : $i, X2 : $i]:
% 0.54/0.76         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.76  thf('70', plain,
% 0.54/0.76      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.54/0.76          = (k1_xboole_0)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.76  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('72', plain,
% 0.54/0.76      ((((k1_xboole_0)
% 0.54/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['54', '59', '70', '71'])).
% 0.54/0.76  thf('73', plain,
% 0.54/0.76      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['51', '72'])).
% 0.54/0.76  thf('74', plain,
% 0.54/0.76      (![X34 : $i, X35 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.54/0.76  thf('75', plain,
% 0.54/0.76      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.54/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['73', '74'])).
% 0.54/0.76  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.76  thf('76', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.54/0.76  thf(t22_subset_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.54/0.76  thf('77', plain,
% 0.54/0.76      (![X41 : $i]:
% 0.54/0.76         ((k2_subset_1 @ X41) = (k3_subset_1 @ X41 @ (k1_subset_1 @ X41)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.54/0.76  thf('78', plain, (![X33 : $i]: ((k2_subset_1 @ X33) = (X33))),
% 0.54/0.76      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.54/0.76  thf('79', plain,
% 0.54/0.76      (![X41 : $i]: ((X41) = (k3_subset_1 @ X41 @ (k1_subset_1 @ X41)))),
% 0.54/0.76      inference('demod', [status(thm)], ['77', '78'])).
% 0.54/0.76  thf('80', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['76', '79'])).
% 0.54/0.76  thf('81', plain,
% 0.54/0.76      ((((u1_struct_0 @ sk_A)
% 0.54/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['75', '80'])).
% 0.54/0.76  thf('82', plain,
% 0.54/0.76      (((((u1_struct_0 @ sk_A)
% 0.54/0.76           = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))
% 0.54/0.76         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['2', '81'])).
% 0.54/0.76  thf('83', plain,
% 0.54/0.76      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.54/0.76          = (k1_xboole_0)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.76  thf('84', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.54/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.54/0.76  thf(involutiveness_k3_subset_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.54/0.76       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.54/0.76  thf('85', plain,
% 0.54/0.76      (![X39 : $i, X40 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X40 @ (k3_subset_1 @ X40 @ X39)) = (X39))
% 0.54/0.76          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.54/0.76      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.54/0.76  thf('86', plain,
% 0.54/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['84', '85'])).
% 0.54/0.76  thf('87', plain,
% 0.54/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['57', '58'])).
% 0.54/0.76  thf('88', plain,
% 0.54/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.54/0.76      inference('demod', [status(thm)], ['86', '87'])).
% 0.54/0.76  thf('89', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.54/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.54/0.76  thf('90', plain,
% 0.54/0.76      (![X37 : $i, X38 : $i]:
% 0.54/0.76         ((m1_subset_1 @ (k3_subset_1 @ X37 @ X38) @ (k1_zfmisc_1 @ X37))
% 0.54/0.76          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.54/0.76  thf('91', plain,
% 0.54/0.76      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['89', '90'])).
% 0.54/0.76  thf('92', plain,
% 0.54/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['57', '58'])).
% 0.54/0.76  thf('93', plain,
% 0.54/0.76      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.54/0.76      inference('demod', [status(thm)], ['91', '92'])).
% 0.54/0.76  thf('94', plain,
% 0.54/0.76      (![X34 : $i, X35 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.54/0.76  thf('95', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.54/0.76           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['93', '94'])).
% 0.54/0.76  thf('96', plain,
% 0.54/0.76      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['88', '95'])).
% 0.54/0.76  thf('97', plain,
% 0.54/0.76      ((((k2_struct_0 @ sk_A)
% 0.54/0.76          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['83', '96'])).
% 0.54/0.76  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('99', plain,
% 0.54/0.76      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['82', '97', '98'])).
% 0.54/0.76  thf('100', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(d1_tops_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( l1_pre_topc @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.54/0.76           ( ( k1_tops_1 @ A @ B ) =
% 0.54/0.76             ( k3_subset_1 @
% 0.54/0.76               ( u1_struct_0 @ A ) @ 
% 0.54/0.76               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.54/0.76  thf('101', plain,
% 0.54/0.76      (![X50 : $i, X51 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.54/0.76          | ((k1_tops_1 @ X51 @ X50)
% 0.54/0.76              = (k3_subset_1 @ (u1_struct_0 @ X51) @ 
% 0.54/0.76                 (k2_pre_topc @ X51 @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50))))
% 0.54/0.76          | ~ (l1_pre_topc @ X51))),
% 0.54/0.76      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.54/0.76  thf('102', plain,
% 0.54/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.76        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.54/0.76            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76               (k2_pre_topc @ sk_A @ 
% 0.54/0.76                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['100', '101'])).
% 0.54/0.76  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('104', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('demod', [status(thm)], ['19', '26'])).
% 0.54/0.76  thf('105', plain,
% 0.54/0.76      (((k1_tops_1 @ sk_A @ sk_B)
% 0.54/0.76         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.54/0.76      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.54/0.76  thf('106', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.54/0.76          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.76             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['99', '105'])).
% 0.54/0.76  thf('107', plain,
% 0.54/0.76      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.54/0.76          = (k2_struct_0 @ sk_A)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['29', '38'])).
% 0.54/0.76  thf('108', plain,
% 0.54/0.76      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['57', '58'])).
% 0.54/0.76  thf('109', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.54/0.76          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.54/0.76  thf('110', plain,
% 0.54/0.76      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.54/0.76          = (k1_xboole_0)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.76  thf('111', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.54/0.76         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['109', '110'])).
% 0.54/0.76  thf('112', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.54/0.76         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf('113', plain,
% 0.54/0.76      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.54/0.76         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.54/0.76             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['111', '112'])).
% 0.54/0.76  thf('114', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.54/0.76       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.54/0.76      inference('simplify', [status(thm)], ['113'])).
% 0.54/0.76  thf('115', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.54/0.76       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.54/0.76      inference('split', [status(esa)], ['3'])).
% 0.54/0.76  thf('116', plain,
% 0.54/0.76      (![X44 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.76  thf('117', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.54/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.54/0.76  thf('118', plain,
% 0.54/0.76      (![X52 : $i, X53 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.54/0.76          | ~ (v1_tops_1 @ X52 @ X53)
% 0.54/0.76          | ((k2_pre_topc @ X53 @ X52) = (k2_struct_0 @ X53))
% 0.54/0.76          | ~ (l1_pre_topc @ X53))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.54/0.76  thf('119', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (l1_pre_topc @ X0)
% 0.54/0.76          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.54/0.76          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['117', '118'])).
% 0.54/0.76  thf('120', plain,
% 0.54/0.76      (![X56 : $i]:
% 0.54/0.76         (((k2_pre_topc @ X56 @ (k2_struct_0 @ X56)) = (k2_struct_0 @ X56))
% 0.54/0.76          | ~ (l1_pre_topc @ X56))),
% 0.54/0.76      inference('cnf', [status(esa)], [t27_tops_1])).
% 0.54/0.76  thf('121', plain,
% 0.54/0.76      (![X44 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.76  thf('122', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.54/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.54/0.76  thf('123', plain,
% 0.54/0.76      (![X52 : $i, X53 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.54/0.76          | ((k2_pre_topc @ X53 @ X52) != (k2_struct_0 @ X53))
% 0.54/0.76          | (v1_tops_1 @ X52 @ X53)
% 0.54/0.76          | ~ (l1_pre_topc @ X53))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.54/0.76  thf('124', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (l1_pre_topc @ X0)
% 0.54/0.76          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.54/0.76          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['122', '123'])).
% 0.54/0.76  thf('125', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) != (k2_struct_0 @ X0))
% 0.54/0.76          | ~ (l1_struct_0 @ X0)
% 0.54/0.76          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.54/0.76          | ~ (l1_pre_topc @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['121', '124'])).
% 0.54/0.76  thf('126', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X0) != (k2_struct_0 @ X0))
% 0.54/0.76          | ~ (l1_pre_topc @ X0)
% 0.54/0.76          | ~ (l1_pre_topc @ X0)
% 0.54/0.76          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.54/0.76          | ~ (l1_struct_0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['120', '125'])).
% 0.54/0.76  thf('127', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (l1_struct_0 @ X0)
% 0.54/0.76          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.54/0.76          | ~ (l1_pre_topc @ X0))),
% 0.54/0.76      inference('simplify', [status(thm)], ['126'])).
% 0.54/0.76  thf('128', plain,
% 0.54/0.76      (![X47 : $i]: ((l1_struct_0 @ X47) | ~ (l1_pre_topc @ X47))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.54/0.76  thf('129', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.54/0.76      inference('clc', [status(thm)], ['127', '128'])).
% 0.54/0.76  thf('130', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.54/0.76          | ~ (l1_pre_topc @ X0))),
% 0.54/0.76      inference('clc', [status(thm)], ['119', '129'])).
% 0.54/0.76  thf('131', plain, (![X36 : $i]: (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))),
% 0.54/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.54/0.76  thf('132', plain,
% 0.54/0.76      (![X48 : $i, X49 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.54/0.76          | (r1_tarski @ X48 @ (k2_pre_topc @ X49 @ X48))
% 0.54/0.76          | ~ (l1_pre_topc @ X49))),
% 0.54/0.76      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.54/0.76  thf('133', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (l1_pre_topc @ X0)
% 0.54/0.76          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.54/0.76             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['131', '132'])).
% 0.54/0.76  thf('134', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.54/0.76          | ~ (l1_pre_topc @ X0)
% 0.54/0.76          | ~ (l1_pre_topc @ X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['130', '133'])).
% 0.54/0.76  thf('135', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (l1_pre_topc @ X0)
% 0.54/0.76          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.54/0.76      inference('simplify', [status(thm)], ['134'])).
% 0.54/0.76  thf('136', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.54/0.76          | ~ (l1_struct_0 @ X0)
% 0.54/0.76          | ~ (l1_pre_topc @ X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['116', '135'])).
% 0.54/0.76  thf('137', plain,
% 0.54/0.76      (![X47 : $i]: ((l1_struct_0 @ X47) | ~ (l1_pre_topc @ X47))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.54/0.76  thf('138', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (l1_pre_topc @ X0)
% 0.54/0.76          | (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.54/0.76      inference('clc', [status(thm)], ['136', '137'])).
% 0.54/0.76  thf('139', plain,
% 0.54/0.76      (![X0 : $i, X2 : $i]:
% 0.54/0.76         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.76      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.76  thf('140', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (l1_pre_topc @ X0)
% 0.54/0.76          | ((k4_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.54/0.76              = (k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['138', '139'])).
% 0.54/0.76  thf('141', plain,
% 0.54/0.76      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.54/0.76      inference('sup+', [status(thm)], ['88', '95'])).
% 0.54/0.76  thf('142', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X0)
% 0.54/0.76            = (k4_xboole_0 @ (k2_struct_0 @ X0) @ k1_xboole_0))
% 0.54/0.76          | ~ (l1_pre_topc @ X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['140', '141'])).
% 0.54/0.76  thf('143', plain,
% 0.54/0.76      (![X44 : $i]:
% 0.54/0.76         (((k2_struct_0 @ X44) = (u1_struct_0 @ X44)) | ~ (l1_struct_0 @ X44))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.76  thf('144', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('split', [status(esa)], ['3'])).
% 0.54/0.76  thf('145', plain,
% 0.54/0.76      ((m1_subset_1 @ 
% 0.54/0.76        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.76  thf('146', plain,
% 0.54/0.76      (![X37 : $i, X38 : $i]:
% 0.54/0.76         ((m1_subset_1 @ (k3_subset_1 @ X37 @ X38) @ (k1_zfmisc_1 @ X37))
% 0.54/0.76          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.54/0.76  thf('147', plain,
% 0.54/0.76      ((m1_subset_1 @ 
% 0.54/0.76        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['145', '146'])).
% 0.54/0.76  thf('148', plain,
% 0.54/0.76      ((m1_subset_1 @ 
% 0.54/0.76        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.76  thf('149', plain,
% 0.54/0.76      (![X34 : $i, X35 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.54/0.76  thf('150', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.54/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['148', '149'])).
% 0.54/0.76  thf('151', plain,
% 0.54/0.76      ((m1_subset_1 @ 
% 0.54/0.76        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['147', '150'])).
% 0.54/0.76  thf('152', plain,
% 0.54/0.76      (((k1_tops_1 @ sk_A @ sk_B)
% 0.54/0.76         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.54/0.76      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.54/0.76  thf('153', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.54/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['148', '149'])).
% 0.54/0.76  thf('154', plain,
% 0.54/0.76      (((k1_tops_1 @ sk_A @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.54/0.76      inference('sup+', [status(thm)], ['152', '153'])).
% 0.54/0.76  thf('155', plain,
% 0.54/0.76      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['151', '154'])).
% 0.54/0.76  thf('156', plain,
% 0.54/0.76      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup+', [status(thm)], ['144', '155'])).
% 0.54/0.76  thf('157', plain,
% 0.54/0.76      (![X34 : $i, X35 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 0.54/0.76          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.54/0.76      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.54/0.76  thf('158', plain,
% 0.54/0.76      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.54/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['156', '157'])).
% 0.54/0.76  thf('159', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['76', '79'])).
% 0.54/0.76  thf('160', plain,
% 0.54/0.76      ((((u1_struct_0 @ sk_A)
% 0.54/0.76          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('demod', [status(thm)], ['158', '159'])).
% 0.54/0.76  thf('161', plain,
% 0.54/0.76      (((((u1_struct_0 @ sk_A)
% 0.54/0.76           = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))
% 0.54/0.76         | ~ (l1_struct_0 @ sk_A)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup+', [status(thm)], ['143', '160'])).
% 0.54/0.76  thf('162', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf('163', plain,
% 0.54/0.76      ((((u1_struct_0 @ sk_A)
% 0.54/0.76          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('demod', [status(thm)], ['161', '162'])).
% 0.54/0.76  thf('164', plain,
% 0.54/0.76      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup+', [status(thm)], ['142', '163'])).
% 0.54/0.76  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('166', plain,
% 0.54/0.76      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('demod', [status(thm)], ['164', '165'])).
% 0.54/0.76  thf('167', plain,
% 0.54/0.76      ((m1_subset_1 @ 
% 0.54/0.76        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.76  thf('168', plain,
% 0.54/0.76      (![X39 : $i, X40 : $i]:
% 0.54/0.76         (((k3_subset_1 @ X40 @ (k3_subset_1 @ X40 @ X39)) = (X39))
% 0.54/0.76          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.54/0.76      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.54/0.76  thf('169', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.54/0.76         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['167', '168'])).
% 0.54/0.76  thf('170', plain,
% 0.54/0.76      (((k1_tops_1 @ sk_A @ sk_B)
% 0.54/0.76         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.76            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.54/0.76      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.54/0.76  thf('171', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.54/0.76         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.54/0.76      inference('demod', [status(thm)], ['169', '170'])).
% 0.54/0.76  thf('172', plain,
% 0.54/0.76      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.54/0.76          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup+', [status(thm)], ['166', '171'])).
% 0.54/0.76  thf('173', plain,
% 0.54/0.76      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('split', [status(esa)], ['3'])).
% 0.54/0.76  thf('174', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['76', '79'])).
% 0.54/0.76  thf('175', plain,
% 0.54/0.76      ((((k2_struct_0 @ sk_A)
% 0.54/0.76          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('demod', [status(thm)], ['172', '173', '174'])).
% 0.54/0.76  thf('176', plain,
% 0.54/0.76      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.54/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.54/0.76  thf('177', plain,
% 0.54/0.76      (![X52 : $i, X53 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 0.54/0.76          | ((k2_pre_topc @ X53 @ X52) != (k2_struct_0 @ X53))
% 0.54/0.76          | (v1_tops_1 @ X52 @ X53)
% 0.54/0.76          | ~ (l1_pre_topc @ X53))),
% 0.54/0.76      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.54/0.76  thf('178', plain,
% 0.54/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.76        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.54/0.76        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.54/0.76            != (k2_struct_0 @ sk_A)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['176', '177'])).
% 0.54/0.76  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('180', plain,
% 0.54/0.76      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.54/0.76        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.54/0.76            != (k2_struct_0 @ sk_A)))),
% 0.54/0.76      inference('demod', [status(thm)], ['178', '179'])).
% 0.54/0.76  thf('181', plain,
% 0.54/0.76      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.54/0.76         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['175', '180'])).
% 0.54/0.76  thf('182', plain,
% 0.54/0.76      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('simplify', [status(thm)], ['181'])).
% 0.54/0.76  thf('183', plain,
% 0.54/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('184', plain,
% 0.54/0.76      (![X54 : $i, X55 : $i]:
% 0.54/0.76         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 0.54/0.76          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X55) @ X54) @ X55)
% 0.54/0.76          | (v2_tops_1 @ X54 @ X55)
% 0.54/0.76          | ~ (l1_pre_topc @ X55))),
% 0.54/0.76      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.54/0.76  thf('185', plain,
% 0.54/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.54/0.76        | (v2_tops_1 @ sk_B @ sk_A)
% 0.54/0.76        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['183', '184'])).
% 0.54/0.76  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('187', plain,
% 0.54/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.54/0.76         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.54/0.76      inference('demod', [status(thm)], ['19', '26'])).
% 0.54/0.76  thf('188', plain,
% 0.54/0.76      (((v2_tops_1 @ sk_B @ sk_A)
% 0.54/0.76        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.54/0.76      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.54/0.76  thf('189', plain,
% 0.54/0.76      (((v2_tops_1 @ sk_B @ sk_A))
% 0.54/0.76         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['182', '188'])).
% 0.54/0.76  thf('190', plain,
% 0.54/0.76      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.54/0.76      inference('split', [status(esa)], ['0'])).
% 0.54/0.76  thf('191', plain,
% 0.54/0.76      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.54/0.76       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.54/0.76      inference('sup-', [status(thm)], ['189', '190'])).
% 0.54/0.76  thf('192', plain, ($false),
% 0.54/0.76      inference('sat_resolution*', [status(thm)], ['1', '114', '115', '191'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.54/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
