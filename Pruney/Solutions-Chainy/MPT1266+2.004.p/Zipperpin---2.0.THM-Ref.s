%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CkcgBhjCpW

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:12 EST 2020

% Result     : Theorem 29.80s
% Output     : Refutation 29.80s
% Verified   : 
% Statistics : Number of formulae       :  181 (1373 expanded)
%              Number of leaves         :   35 ( 444 expanded)
%              Depth                    :   26
%              Number of atoms          : 1418 (10610 expanded)
%              Number of equality atoms :  107 ( 866 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v1_tops_1 @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k2_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('8',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tops_1 @ X37 @ X38 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = ( k3_subset_1 @ X18 @ ( k1_subset_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('13',plain,(
    ! [X18: $i] :
      ( X18
      = ( k3_subset_1 @ X18 @ ( k1_subset_1 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v2_tops_1 @ X31 @ X32 )
      | ~ ( v1_xboole_0 @ X31 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc2_tops_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['6','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t47_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) )
        = ( k1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X44: $i] :
      ( ( ( k1_tops_1 @ X44 @ ( k1_struct_0 @ X44 ) )
        = ( k1_struct_0 @ X44 ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t47_tops_1])).

thf(fc8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_xboole_0 @ ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) ) ) )).

thf('26',plain,(
    ! [X41: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ X41 @ ( k1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc8_tops_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X41: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ X41 @ ( k1_struct_0 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc8_tops_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_tops_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('39',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_subset_1 @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('44',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( X18
      = ( k3_subset_1 @ X18 @ ( k1_subset_1 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_xboole_0 @ ( k1_subset_1 @ X0 ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','48'])).

thf('50',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('55',plain,
    ( ( k1_xboole_0
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['22','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tops_1 @ X37 @ X38 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('68',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v1_tops_1 @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k2_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['57','79'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('85',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('86',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('87',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( k1_xboole_0
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['6','21'])).

thf('93',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('94',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t64_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( ( k3_subset_1 @ A @ B )
              = ( k3_subset_1 @ A @ C ) )
           => ( B = C ) ) ) ) )).

thf('99',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( X22 = X20 )
      | ( ( k3_subset_1 @ X21 @ X22 )
       != ( k3_subset_1 @ X21 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t64_subset_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X1 )
       != ( k3_subset_1 @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('102',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X1 )
       != k1_xboole_0 )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['100','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('113',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','111','112'])).

thf('114',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('115',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('117',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('118',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('119',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','119'])).

thf('121',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['85','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('123',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('125',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ X35 )
       != ( k2_struct_0 @ X36 ) )
      | ( v1_tops_1 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('130',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('131',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','131'])).

thf('133',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ X38 )
      | ( v2_tops_1 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('140',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','140'])).

thf('142',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('143',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','83','84','143'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CkcgBhjCpW
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:14:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 29.80/30.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 29.80/30.04  % Solved by: fo/fo7.sh
% 29.80/30.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.80/30.04  % done 36328 iterations in 29.566s
% 29.80/30.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 29.80/30.04  % SZS output start Refutation
% 29.80/30.04  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 29.80/30.04  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 29.80/30.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 29.80/30.04  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 29.80/30.04  thf(sk_B_type, type, sk_B: $i).
% 29.80/30.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.80/30.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 29.80/30.04  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 29.80/30.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.80/30.04  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 29.80/30.04  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 29.80/30.04  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 29.80/30.04  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 29.80/30.04  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 29.80/30.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 29.80/30.04  thf(sk_A_type, type, sk_A: $i).
% 29.80/30.04  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 29.80/30.04  thf(t84_tops_1, conjecture,
% 29.80/30.04    (![A:$i]:
% 29.80/30.04     ( ( l1_pre_topc @ A ) =>
% 29.80/30.04       ( ![B:$i]:
% 29.80/30.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.80/30.04           ( ( v2_tops_1 @ B @ A ) <=>
% 29.80/30.04             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 29.80/30.04  thf(zf_stmt_0, negated_conjecture,
% 29.80/30.04    (~( ![A:$i]:
% 29.80/30.04        ( ( l1_pre_topc @ A ) =>
% 29.80/30.04          ( ![B:$i]:
% 29.80/30.04            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.80/30.04              ( ( v2_tops_1 @ B @ A ) <=>
% 29.80/30.04                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 29.80/30.04    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 29.80/30.04  thf('0', plain,
% 29.80/30.04      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 29.80/30.04        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('1', plain,
% 29.80/30.04      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 29.80/30.04       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 29.80/30.04      inference('split', [status(esa)], ['0'])).
% 29.80/30.04  thf(dt_k2_subset_1, axiom,
% 29.80/30.04    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 29.80/30.04  thf('2', plain,
% 29.80/30.04      (![X13 : $i]: (m1_subset_1 @ (k2_subset_1 @ X13) @ (k1_zfmisc_1 @ X13))),
% 29.80/30.04      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 29.80/30.04  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 29.80/30.04  thf('3', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 29.80/30.04      inference('cnf', [status(esa)], [d4_subset_1])).
% 29.80/30.04  thf('4', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 29.80/30.04      inference('demod', [status(thm)], ['2', '3'])).
% 29.80/30.04  thf(d3_tops_1, axiom,
% 29.80/30.04    (![A:$i]:
% 29.80/30.04     ( ( l1_pre_topc @ A ) =>
% 29.80/30.04       ( ![B:$i]:
% 29.80/30.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.80/30.04           ( ( v1_tops_1 @ B @ A ) <=>
% 29.80/30.04             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 29.80/30.04  thf('5', plain,
% 29.80/30.04      (![X35 : $i, X36 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 29.80/30.04          | ~ (v1_tops_1 @ X35 @ X36)
% 29.80/30.04          | ((k2_pre_topc @ X36 @ X35) = (k2_struct_0 @ X36))
% 29.80/30.04          | ~ (l1_pre_topc @ X36))),
% 29.80/30.04      inference('cnf', [status(esa)], [d3_tops_1])).
% 29.80/30.04  thf('6', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 29.80/30.04          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 29.80/30.04      inference('sup-', [status(thm)], ['4', '5'])).
% 29.80/30.04  thf(t4_subset_1, axiom,
% 29.80/30.04    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 29.80/30.04  thf('7', plain,
% 29.80/30.04      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 29.80/30.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 29.80/30.04  thf(d4_tops_1, axiom,
% 29.80/30.04    (![A:$i]:
% 29.80/30.04     ( ( l1_pre_topc @ A ) =>
% 29.80/30.04       ( ![B:$i]:
% 29.80/30.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.80/30.04           ( ( v2_tops_1 @ B @ A ) <=>
% 29.80/30.04             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 29.80/30.04  thf('8', plain,
% 29.80/30.04      (![X37 : $i, X38 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 29.80/30.04          | ~ (v2_tops_1 @ X37 @ X38)
% 29.80/30.04          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X38) @ X37) @ X38)
% 29.80/30.04          | ~ (l1_pre_topc @ X38))),
% 29.80/30.04      inference('cnf', [status(esa)], [d4_tops_1])).
% 29.80/30.04  thf('9', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0)
% 29.80/30.04          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 29.80/30.04      inference('sup-', [status(thm)], ['7', '8'])).
% 29.80/30.04  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 29.80/30.04  thf('10', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 29.80/30.04      inference('cnf', [status(esa)], [d3_subset_1])).
% 29.80/30.04  thf(t22_subset_1, axiom,
% 29.80/30.04    (![A:$i]:
% 29.80/30.04     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 29.80/30.04  thf('11', plain,
% 29.80/30.04      (![X18 : $i]:
% 29.80/30.04         ((k2_subset_1 @ X18) = (k3_subset_1 @ X18 @ (k1_subset_1 @ X18)))),
% 29.80/30.04      inference('cnf', [status(esa)], [t22_subset_1])).
% 29.80/30.04  thf('12', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 29.80/30.04      inference('cnf', [status(esa)], [d4_subset_1])).
% 29.80/30.04  thf('13', plain,
% 29.80/30.04      (![X18 : $i]: ((X18) = (k3_subset_1 @ X18 @ (k1_subset_1 @ X18)))),
% 29.80/30.04      inference('demod', [status(thm)], ['11', '12'])).
% 29.80/30.04  thf('14', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 29.80/30.04      inference('sup+', [status(thm)], ['10', '13'])).
% 29.80/30.04  thf('15', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 29.80/30.04          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 29.80/30.04      inference('demod', [status(thm)], ['9', '14'])).
% 29.80/30.04  thf('16', plain,
% 29.80/30.04      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 29.80/30.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 29.80/30.04  thf(cc2_tops_1, axiom,
% 29.80/30.04    (![A:$i]:
% 29.80/30.04     ( ( l1_pre_topc @ A ) =>
% 29.80/30.04       ( ![B:$i]:
% 29.80/30.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.80/30.04           ( ( v1_xboole_0 @ B ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 29.80/30.04  thf('17', plain,
% 29.80/30.04      (![X31 : $i, X32 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 29.80/30.04          | (v2_tops_1 @ X31 @ X32)
% 29.80/30.04          | ~ (v1_xboole_0 @ X31)
% 29.80/30.04          | ~ (l1_pre_topc @ X32))),
% 29.80/30.04      inference('cnf', [status(esa)], [cc2_tops_1])).
% 29.80/30.04  thf('18', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | ~ (v1_xboole_0 @ k1_xboole_0)
% 29.80/30.04          | (v2_tops_1 @ k1_xboole_0 @ X0))),
% 29.80/30.04      inference('sup-', [status(thm)], ['16', '17'])).
% 29.80/30.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 29.80/30.04  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 29.80/30.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 29.80/30.04  thf('20', plain,
% 29.80/30.04      (![X0 : $i]: (~ (l1_pre_topc @ X0) | (v2_tops_1 @ k1_xboole_0 @ X0))),
% 29.80/30.04      inference('demod', [status(thm)], ['18', '19'])).
% 29.80/30.04  thf('21', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 29.80/30.04      inference('clc', [status(thm)], ['15', '20'])).
% 29.80/30.04  thf('22', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 29.80/30.04          | ~ (l1_pre_topc @ X0))),
% 29.80/30.04      inference('clc', [status(thm)], ['6', '21'])).
% 29.80/30.04  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf(l13_xboole_0, axiom,
% 29.80/30.04    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 29.80/30.04  thf('24', plain,
% 29.80/30.04      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 29.80/30.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 29.80/30.04  thf(t47_tops_1, axiom,
% 29.80/30.04    (![A:$i]:
% 29.80/30.04     ( ( l1_pre_topc @ A ) =>
% 29.80/30.04       ( ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) = ( k1_struct_0 @ A ) ) ))).
% 29.80/30.04  thf('25', plain,
% 29.80/30.04      (![X44 : $i]:
% 29.80/30.04         (((k1_tops_1 @ X44 @ (k1_struct_0 @ X44)) = (k1_struct_0 @ X44))
% 29.80/30.04          | ~ (l1_pre_topc @ X44))),
% 29.80/30.04      inference('cnf', [status(esa)], [t47_tops_1])).
% 29.80/30.04  thf(fc8_tops_1, axiom,
% 29.80/30.04    (![A:$i]:
% 29.80/30.04     ( ( l1_pre_topc @ A ) =>
% 29.80/30.04       ( v1_xboole_0 @ ( k1_tops_1 @ A @ ( k1_struct_0 @ A ) ) ) ))).
% 29.80/30.04  thf('26', plain,
% 29.80/30.04      (![X41 : $i]:
% 29.80/30.04         ((v1_xboole_0 @ (k1_tops_1 @ X41 @ (k1_struct_0 @ X41)))
% 29.80/30.04          | ~ (l1_pre_topc @ X41))),
% 29.80/30.04      inference('cnf', [status(esa)], [fc8_tops_1])).
% 29.80/30.04  thf('27', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         ((v1_xboole_0 @ (k1_struct_0 @ X0))
% 29.80/30.04          | ~ (l1_pre_topc @ X0)
% 29.80/30.04          | ~ (l1_pre_topc @ X0))),
% 29.80/30.04      inference('sup+', [status(thm)], ['25', '26'])).
% 29.80/30.04  thf('28', plain,
% 29.80/30.04      (![X0 : $i]: (~ (l1_pre_topc @ X0) | (v1_xboole_0 @ (k1_struct_0 @ X0)))),
% 29.80/30.04      inference('simplify', [status(thm)], ['27'])).
% 29.80/30.04  thf('29', plain,
% 29.80/30.04      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 29.80/30.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 29.80/30.04  thf('30', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0) | ((k1_struct_0 @ X0) = (k1_xboole_0)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['28', '29'])).
% 29.80/30.04  thf('31', plain,
% 29.80/30.04      (![X41 : $i]:
% 29.80/30.04         ((v1_xboole_0 @ (k1_tops_1 @ X41 @ (k1_struct_0 @ X41)))
% 29.80/30.04          | ~ (l1_pre_topc @ X41))),
% 29.80/30.04      inference('cnf', [status(esa)], [fc8_tops_1])).
% 29.80/30.04  thf('32', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         ((v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0))
% 29.80/30.04          | ~ (l1_pre_topc @ X0)
% 29.80/30.04          | ~ (l1_pre_topc @ X0))),
% 29.80/30.04      inference('sup+', [status(thm)], ['30', '31'])).
% 29.80/30.04  thf('33', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0) | (v1_xboole_0 @ (k1_tops_1 @ X0 @ k1_xboole_0)))),
% 29.80/30.04      inference('simplify', [status(thm)], ['32'])).
% 29.80/30.04  thf('34', plain,
% 29.80/30.04      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 29.80/30.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 29.80/30.04  thf('35', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['33', '34'])).
% 29.80/30.04  thf('36', plain,
% 29.80/30.04      (![X0 : $i, X1 : $i]:
% 29.80/30.04         (((k1_tops_1 @ X1 @ X0) = (k1_xboole_0))
% 29.80/30.04          | ~ (v1_xboole_0 @ X0)
% 29.80/30.04          | ~ (l1_pre_topc @ X1))),
% 29.80/30.04      inference('sup+', [status(thm)], ['24', '35'])).
% 29.80/30.04  thf('37', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (v1_xboole_0 @ X0) | ((k1_tops_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['23', '36'])).
% 29.80/30.04  thf('38', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 29.80/30.04      inference('cnf', [status(esa)], [d3_subset_1])).
% 29.80/30.04  thf('39', plain,
% 29.80/30.04      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 29.80/30.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 29.80/30.04  thf('40', plain,
% 29.80/30.04      (![X0 : $i, X1 : $i]:
% 29.80/30.04         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 29.80/30.04      inference('sup+', [status(thm)], ['38', '39'])).
% 29.80/30.04  thf(d1_tops_1, axiom,
% 29.80/30.04    (![A:$i]:
% 29.80/30.04     ( ( l1_pre_topc @ A ) =>
% 29.80/30.04       ( ![B:$i]:
% 29.80/30.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.80/30.04           ( ( k1_tops_1 @ A @ B ) =
% 29.80/30.04             ( k3_subset_1 @
% 29.80/30.04               ( u1_struct_0 @ A ) @ 
% 29.80/30.04               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 29.80/30.04  thf('41', plain,
% 29.80/30.04      (![X33 : $i, X34 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 29.80/30.04          | ((k1_tops_1 @ X34 @ X33)
% 29.80/30.04              = (k3_subset_1 @ (u1_struct_0 @ X34) @ 
% 29.80/30.04                 (k2_pre_topc @ X34 @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33))))
% 29.80/30.04          | ~ (l1_pre_topc @ X34))),
% 29.80/30.04      inference('cnf', [status(esa)], [d1_tops_1])).
% 29.80/30.04  thf('42', plain,
% 29.80/30.04      (![X0 : $i, X1 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | ((k1_tops_1 @ X0 @ (k1_subset_1 @ X1))
% 29.80/30.04              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 29.80/30.04                 (k2_pre_topc @ X0 @ 
% 29.80/30.04                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (k1_subset_1 @ X1))))))),
% 29.80/30.04      inference('sup-', [status(thm)], ['40', '41'])).
% 29.80/30.04  thf('43', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 29.80/30.04      inference('cnf', [status(esa)], [d3_subset_1])).
% 29.80/30.04  thf('44', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 29.80/30.04      inference('cnf', [status(esa)], [d3_subset_1])).
% 29.80/30.04  thf('45', plain,
% 29.80/30.04      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 29.80/30.04      inference('sup+', [status(thm)], ['43', '44'])).
% 29.80/30.04  thf('46', plain,
% 29.80/30.04      (![X18 : $i]: ((X18) = (k3_subset_1 @ X18 @ (k1_subset_1 @ X18)))),
% 29.80/30.04      inference('demod', [status(thm)], ['11', '12'])).
% 29.80/30.04  thf('47', plain,
% 29.80/30.04      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 29.80/30.04      inference('sup+', [status(thm)], ['45', '46'])).
% 29.80/30.04  thf('48', plain,
% 29.80/30.04      (![X0 : $i, X1 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | ((k1_tops_1 @ X0 @ (k1_subset_1 @ X1))
% 29.80/30.04              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 29.80/30.04                 (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 29.80/30.04      inference('demod', [status(thm)], ['42', '47'])).
% 29.80/30.04  thf('49', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (((k1_xboole_0)
% 29.80/30.04            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.80/30.04               (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))))
% 29.80/30.04          | ~ (v1_xboole_0 @ (k1_subset_1 @ X0))
% 29.80/30.04          | ~ (l1_pre_topc @ sk_A))),
% 29.80/30.04      inference('sup+', [status(thm)], ['37', '48'])).
% 29.80/30.04  thf('50', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 29.80/30.04      inference('cnf', [status(esa)], [d3_subset_1])).
% 29.80/30.04  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 29.80/30.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 29.80/30.04  thf('52', plain, (![X0 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X0))),
% 29.80/30.04      inference('sup+', [status(thm)], ['50', '51'])).
% 29.80/30.04  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('54', plain,
% 29.80/30.04      (((k1_xboole_0)
% 29.80/30.04         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.80/30.04            (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))))),
% 29.80/30.04      inference('demod', [status(thm)], ['49', '52', '53'])).
% 29.80/30.04  thf('55', plain,
% 29.80/30.04      ((((k1_xboole_0)
% 29.80/30.04          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 29.80/30.04        | ~ (l1_pre_topc @ sk_A))),
% 29.80/30.04      inference('sup+', [status(thm)], ['22', '54'])).
% 29.80/30.04  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('57', plain,
% 29.80/30.04      (((k1_xboole_0)
% 29.80/30.04         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 29.80/30.04      inference('demod', [status(thm)], ['55', '56'])).
% 29.80/30.04  thf('58', plain,
% 29.80/30.04      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('59', plain,
% 29.80/30.04      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 29.80/30.04      inference('split', [status(esa)], ['58'])).
% 29.80/30.04  thf('60', plain,
% 29.80/30.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('61', plain,
% 29.80/30.04      (![X37 : $i, X38 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 29.80/30.04          | ~ (v2_tops_1 @ X37 @ X38)
% 29.80/30.04          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X38) @ X37) @ X38)
% 29.80/30.04          | ~ (l1_pre_topc @ X38))),
% 29.80/30.04      inference('cnf', [status(esa)], [d4_tops_1])).
% 29.80/30.04  thf('62', plain,
% 29.80/30.04      ((~ (l1_pre_topc @ sk_A)
% 29.80/30.04        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 29.80/30.04        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 29.80/30.04      inference('sup-', [status(thm)], ['60', '61'])).
% 29.80/30.04  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('64', plain,
% 29.80/30.04      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 29.80/30.04        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 29.80/30.04      inference('demod', [status(thm)], ['62', '63'])).
% 29.80/30.04  thf('65', plain,
% 29.80/30.04      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 29.80/30.04         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['59', '64'])).
% 29.80/30.04  thf('66', plain,
% 29.80/30.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf(dt_k3_subset_1, axiom,
% 29.80/30.04    (![A:$i,B:$i]:
% 29.80/30.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 29.80/30.04       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 29.80/30.04  thf('67', plain,
% 29.80/30.04      (![X14 : $i, X15 : $i]:
% 29.80/30.04         ((m1_subset_1 @ (k3_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 29.80/30.04          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 29.80/30.04      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 29.80/30.04  thf('68', plain,
% 29.80/30.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 29.80/30.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['66', '67'])).
% 29.80/30.04  thf('69', plain,
% 29.80/30.04      (![X35 : $i, X36 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 29.80/30.04          | ~ (v1_tops_1 @ X35 @ X36)
% 29.80/30.04          | ((k2_pre_topc @ X36 @ X35) = (k2_struct_0 @ X36))
% 29.80/30.04          | ~ (l1_pre_topc @ X36))),
% 29.80/30.04      inference('cnf', [status(esa)], [d3_tops_1])).
% 29.80/30.04  thf('70', plain,
% 29.80/30.04      ((~ (l1_pre_topc @ sk_A)
% 29.80/30.04        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 29.80/30.04            = (k2_struct_0 @ sk_A))
% 29.80/30.04        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 29.80/30.04      inference('sup-', [status(thm)], ['68', '69'])).
% 29.80/30.04  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('72', plain,
% 29.80/30.04      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 29.80/30.04          = (k2_struct_0 @ sk_A))
% 29.80/30.04        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 29.80/30.04      inference('demod', [status(thm)], ['70', '71'])).
% 29.80/30.04  thf('73', plain,
% 29.80/30.04      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 29.80/30.04          = (k2_struct_0 @ sk_A)))
% 29.80/30.04         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['65', '72'])).
% 29.80/30.04  thf('74', plain,
% 29.80/30.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('75', plain,
% 29.80/30.04      (![X33 : $i, X34 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 29.80/30.04          | ((k1_tops_1 @ X34 @ X33)
% 29.80/30.04              = (k3_subset_1 @ (u1_struct_0 @ X34) @ 
% 29.80/30.04                 (k2_pre_topc @ X34 @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33))))
% 29.80/30.04          | ~ (l1_pre_topc @ X34))),
% 29.80/30.04      inference('cnf', [status(esa)], [d1_tops_1])).
% 29.80/30.04  thf('76', plain,
% 29.80/30.04      ((~ (l1_pre_topc @ sk_A)
% 29.80/30.04        | ((k1_tops_1 @ sk_A @ sk_B)
% 29.80/30.04            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.80/30.04               (k2_pre_topc @ sk_A @ 
% 29.80/30.04                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 29.80/30.04      inference('sup-', [status(thm)], ['74', '75'])).
% 29.80/30.04  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('78', plain,
% 29.80/30.04      (((k1_tops_1 @ sk_A @ sk_B)
% 29.80/30.04         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.80/30.04            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 29.80/30.04      inference('demod', [status(thm)], ['76', '77'])).
% 29.80/30.04  thf('79', plain,
% 29.80/30.04      ((((k1_tops_1 @ sk_A @ sk_B)
% 29.80/30.04          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 29.80/30.04         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 29.80/30.04      inference('sup+', [status(thm)], ['73', '78'])).
% 29.80/30.04  thf('80', plain,
% 29.80/30.04      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 29.80/30.04         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 29.80/30.04      inference('sup+', [status(thm)], ['57', '79'])).
% 29.80/30.04  thf('81', plain,
% 29.80/30.04      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 29.80/30.04         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 29.80/30.04      inference('split', [status(esa)], ['0'])).
% 29.80/30.04  thf('82', plain,
% 29.80/30.04      ((((k1_xboole_0) != (k1_xboole_0)))
% 29.80/30.04         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 29.80/30.04             ((v2_tops_1 @ sk_B @ sk_A)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['80', '81'])).
% 29.80/30.04  thf('83', plain,
% 29.80/30.04      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 29.80/30.04       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 29.80/30.04      inference('simplify', [status(thm)], ['82'])).
% 29.80/30.04  thf('84', plain,
% 29.80/30.04      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 29.80/30.04       ((v2_tops_1 @ sk_B @ sk_A))),
% 29.80/30.04      inference('split', [status(esa)], ['58'])).
% 29.80/30.04  thf('85', plain,
% 29.80/30.04      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 29.80/30.04         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 29.80/30.04      inference('split', [status(esa)], ['58'])).
% 29.80/30.04  thf('86', plain,
% 29.80/30.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 29.80/30.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['66', '67'])).
% 29.80/30.04  thf(dt_k2_pre_topc, axiom,
% 29.80/30.04    (![A:$i,B:$i]:
% 29.80/30.04     ( ( ( l1_pre_topc @ A ) & 
% 29.80/30.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 29.80/30.04       ( m1_subset_1 @
% 29.80/30.04         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 29.80/30.04  thf('87', plain,
% 29.80/30.04      (![X29 : $i, X30 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X29)
% 29.80/30.04          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 29.80/30.04          | (m1_subset_1 @ (k2_pre_topc @ X29 @ X30) @ 
% 29.80/30.04             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 29.80/30.04      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 29.80/30.04  thf('88', plain,
% 29.80/30.04      (((m1_subset_1 @ 
% 29.80/30.04         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 29.80/30.04         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.80/30.04        | ~ (l1_pre_topc @ sk_A))),
% 29.80/30.04      inference('sup-', [status(thm)], ['86', '87'])).
% 29.80/30.04  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('90', plain,
% 29.80/30.04      ((m1_subset_1 @ 
% 29.80/30.04        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 29.80/30.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('demod', [status(thm)], ['88', '89'])).
% 29.80/30.04  thf('91', plain,
% 29.80/30.04      (((k1_xboole_0)
% 29.80/30.04         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 29.80/30.04      inference('demod', [status(thm)], ['55', '56'])).
% 29.80/30.04  thf('92', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 29.80/30.04          | ~ (l1_pre_topc @ X0))),
% 29.80/30.04      inference('clc', [status(thm)], ['6', '21'])).
% 29.80/30.04  thf('93', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 29.80/30.04      inference('demod', [status(thm)], ['2', '3'])).
% 29.80/30.04  thf('94', plain,
% 29.80/30.04      (![X29 : $i, X30 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X29)
% 29.80/30.04          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 29.80/30.04          | (m1_subset_1 @ (k2_pre_topc @ X29 @ X30) @ 
% 29.80/30.04             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 29.80/30.04      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 29.80/30.04  thf('95', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 29.80/30.04           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 29.80/30.04          | ~ (l1_pre_topc @ X0))),
% 29.80/30.04      inference('sup-', [status(thm)], ['93', '94'])).
% 29.80/30.04  thf('96', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 29.80/30.04           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 29.80/30.04          | ~ (l1_pre_topc @ X0)
% 29.80/30.04          | ~ (l1_pre_topc @ X0))),
% 29.80/30.04      inference('sup+', [status(thm)], ['92', '95'])).
% 29.80/30.04  thf('97', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 29.80/30.04             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 29.80/30.04      inference('simplify', [status(thm)], ['96'])).
% 29.80/30.04  thf('98', plain, (![X13 : $i]: (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X13))),
% 29.80/30.04      inference('demod', [status(thm)], ['2', '3'])).
% 29.80/30.04  thf(t64_subset_1, axiom,
% 29.80/30.04    (![A:$i,B:$i]:
% 29.80/30.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 29.80/30.04       ( ![C:$i]:
% 29.80/30.04         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 29.80/30.04           ( ( ( k3_subset_1 @ A @ B ) = ( k3_subset_1 @ A @ C ) ) =>
% 29.80/30.04             ( ( B ) = ( C ) ) ) ) ) ))).
% 29.80/30.04  thf('99', plain,
% 29.80/30.04      (![X20 : $i, X21 : $i, X22 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 29.80/30.04          | ((X22) = (X20))
% 29.80/30.04          | ((k3_subset_1 @ X21 @ X22) != (k3_subset_1 @ X21 @ X20))
% 29.80/30.04          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 29.80/30.04      inference('cnf', [status(esa)], [t64_subset_1])).
% 29.80/30.04  thf('100', plain,
% 29.80/30.04      (![X0 : $i, X1 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 29.80/30.04          | ((k3_subset_1 @ X0 @ X1) != (k3_subset_1 @ X0 @ X0))
% 29.80/30.04          | ((X1) = (X0)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['98', '99'])).
% 29.80/30.04  thf('101', plain,
% 29.80/30.04      (![X19 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 29.80/30.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 29.80/30.04  thf(involutiveness_k3_subset_1, axiom,
% 29.80/30.04    (![A:$i,B:$i]:
% 29.80/30.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 29.80/30.04       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 29.80/30.04  thf('102', plain,
% 29.80/30.04      (![X16 : $i, X17 : $i]:
% 29.80/30.04         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 29.80/30.04          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 29.80/30.04      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 29.80/30.04  thf('103', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 29.80/30.04      inference('sup-', [status(thm)], ['101', '102'])).
% 29.80/30.04  thf('104', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 29.80/30.04      inference('sup+', [status(thm)], ['10', '13'])).
% 29.80/30.04  thf('105', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 29.80/30.04      inference('demod', [status(thm)], ['103', '104'])).
% 29.80/30.04  thf('106', plain,
% 29.80/30.04      (![X0 : $i, X1 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 29.80/30.04          | ((k3_subset_1 @ X0 @ X1) != (k1_xboole_0))
% 29.80/30.04          | ((X1) = (X0)))),
% 29.80/30.04      inference('demod', [status(thm)], ['100', '105'])).
% 29.80/30.04  thf('107', plain,
% 29.80/30.04      (![X0 : $i]:
% 29.80/30.04         (~ (l1_pre_topc @ X0)
% 29.80/30.04          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 29.80/30.04          | ((k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 29.80/30.04              != (k1_xboole_0)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['97', '106'])).
% 29.80/30.04  thf('108', plain,
% 29.80/30.04      ((((k1_xboole_0) != (k1_xboole_0))
% 29.80/30.04        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 29.80/30.04        | ~ (l1_pre_topc @ sk_A))),
% 29.80/30.04      inference('sup-', [status(thm)], ['91', '107'])).
% 29.80/30.04  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('110', plain,
% 29.80/30.04      ((((k1_xboole_0) != (k1_xboole_0))
% 29.80/30.04        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('demod', [status(thm)], ['108', '109'])).
% 29.80/30.04  thf('111', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.80/30.04      inference('simplify', [status(thm)], ['110'])).
% 29.80/30.04  thf('112', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.80/30.04      inference('simplify', [status(thm)], ['110'])).
% 29.80/30.04  thf('113', plain,
% 29.80/30.04      ((m1_subset_1 @ 
% 29.80/30.04        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 29.80/30.04        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 29.80/30.04      inference('demod', [status(thm)], ['90', '111', '112'])).
% 29.80/30.04  thf('114', plain,
% 29.80/30.04      (![X16 : $i, X17 : $i]:
% 29.80/30.04         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 29.80/30.04          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 29.80/30.04      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 29.80/30.04  thf('115', plain,
% 29.80/30.04      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 29.80/30.04         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 29.80/30.04          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 29.80/30.04         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['113', '114'])).
% 29.80/30.04  thf('116', plain,
% 29.80/30.04      (((k1_tops_1 @ sk_A @ sk_B)
% 29.80/30.04         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.80/30.04            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 29.80/30.04      inference('demod', [status(thm)], ['76', '77'])).
% 29.80/30.04  thf('117', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.80/30.04      inference('simplify', [status(thm)], ['110'])).
% 29.80/30.04  thf('118', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.80/30.04      inference('simplify', [status(thm)], ['110'])).
% 29.80/30.04  thf('119', plain,
% 29.80/30.04      (((k1_tops_1 @ sk_A @ sk_B)
% 29.80/30.04         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 29.80/30.04            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 29.80/30.04      inference('demod', [status(thm)], ['116', '117', '118'])).
% 29.80/30.04  thf('120', plain,
% 29.80/30.04      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 29.80/30.04         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 29.80/30.04      inference('demod', [status(thm)], ['115', '119'])).
% 29.80/30.04  thf('121', plain,
% 29.80/30.04      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 29.80/30.04          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 29.80/30.04         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 29.80/30.04      inference('sup+', [status(thm)], ['85', '120'])).
% 29.80/30.04  thf('122', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 29.80/30.04      inference('sup+', [status(thm)], ['10', '13'])).
% 29.80/30.04  thf('123', plain,
% 29.80/30.04      ((((k2_struct_0 @ sk_A)
% 29.80/30.04          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 29.80/30.04         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 29.80/30.04      inference('demod', [status(thm)], ['121', '122'])).
% 29.80/30.04  thf('124', plain,
% 29.80/30.04      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 29.80/30.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['66', '67'])).
% 29.80/30.04  thf('125', plain,
% 29.80/30.04      (![X35 : $i, X36 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 29.80/30.04          | ((k2_pre_topc @ X36 @ X35) != (k2_struct_0 @ X36))
% 29.80/30.04          | (v1_tops_1 @ X35 @ X36)
% 29.80/30.04          | ~ (l1_pre_topc @ X36))),
% 29.80/30.04      inference('cnf', [status(esa)], [d3_tops_1])).
% 29.80/30.04  thf('126', plain,
% 29.80/30.04      ((~ (l1_pre_topc @ sk_A)
% 29.80/30.04        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 29.80/30.04        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 29.80/30.04            != (k2_struct_0 @ sk_A)))),
% 29.80/30.04      inference('sup-', [status(thm)], ['124', '125'])).
% 29.80/30.04  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('128', plain,
% 29.80/30.04      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 29.80/30.04        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 29.80/30.04            != (k2_struct_0 @ sk_A)))),
% 29.80/30.04      inference('demod', [status(thm)], ['126', '127'])).
% 29.80/30.04  thf('129', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.80/30.04      inference('simplify', [status(thm)], ['110'])).
% 29.80/30.04  thf('130', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.80/30.04      inference('simplify', [status(thm)], ['110'])).
% 29.80/30.04  thf('131', plain,
% 29.80/30.04      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 29.80/30.04        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 29.80/30.04            != (k2_struct_0 @ sk_A)))),
% 29.80/30.04      inference('demod', [status(thm)], ['128', '129', '130'])).
% 29.80/30.04  thf('132', plain,
% 29.80/30.04      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 29.80/30.04         | (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 29.80/30.04         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 29.80/30.04      inference('sup-', [status(thm)], ['123', '131'])).
% 29.80/30.04  thf('133', plain,
% 29.80/30.04      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 29.80/30.04         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 29.80/30.04      inference('simplify', [status(thm)], ['132'])).
% 29.80/30.04  thf('134', plain,
% 29.80/30.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('135', plain,
% 29.80/30.04      (![X37 : $i, X38 : $i]:
% 29.80/30.04         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 29.80/30.04          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X38) @ X37) @ X38)
% 29.80/30.04          | (v2_tops_1 @ X37 @ X38)
% 29.80/30.04          | ~ (l1_pre_topc @ X38))),
% 29.80/30.04      inference('cnf', [status(esa)], [d4_tops_1])).
% 29.80/30.04  thf('136', plain,
% 29.80/30.04      ((~ (l1_pre_topc @ sk_A)
% 29.80/30.04        | (v2_tops_1 @ sk_B @ sk_A)
% 29.80/30.04        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 29.80/30.04      inference('sup-', [status(thm)], ['134', '135'])).
% 29.80/30.04  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 29.80/30.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.80/30.04  thf('138', plain,
% 29.80/30.04      (((v2_tops_1 @ sk_B @ sk_A)
% 29.80/30.04        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 29.80/30.04      inference('demod', [status(thm)], ['136', '137'])).
% 29.80/30.04  thf('139', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 29.80/30.04      inference('simplify', [status(thm)], ['110'])).
% 29.80/30.04  thf('140', plain,
% 29.80/30.04      (((v2_tops_1 @ sk_B @ sk_A)
% 29.80/30.04        | ~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 29.80/30.04      inference('demod', [status(thm)], ['138', '139'])).
% 29.80/30.04  thf('141', plain,
% 29.80/30.04      (((v2_tops_1 @ sk_B @ sk_A))
% 29.80/30.04         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 29.80/30.04      inference('sup-', [status(thm)], ['133', '140'])).
% 29.80/30.04  thf('142', plain,
% 29.80/30.04      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 29.80/30.04      inference('split', [status(esa)], ['0'])).
% 29.80/30.04  thf('143', plain,
% 29.80/30.04      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 29.80/30.04       ((v2_tops_1 @ sk_B @ sk_A))),
% 29.80/30.04      inference('sup-', [status(thm)], ['141', '142'])).
% 29.80/30.04  thf('144', plain, ($false),
% 29.80/30.04      inference('sat_resolution*', [status(thm)], ['1', '83', '84', '143'])).
% 29.80/30.04  
% 29.80/30.04  % SZS output end Refutation
% 29.80/30.04  
% 29.80/30.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
