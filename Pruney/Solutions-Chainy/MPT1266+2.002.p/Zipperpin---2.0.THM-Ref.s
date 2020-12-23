%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fcJSAuM43r

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:12 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  213 (1575 expanded)
%              Number of leaves         :   36 ( 489 expanded)
%              Depth                    :   26
%              Number of atoms          : 1791 (14444 expanded)
%              Number of equality atoms :  137 (1028 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tops_1 @ X30 @ X31 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('14',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v1_tops_1 @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = ( k2_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('27',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v1_tops_1 @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = ( k2_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('32',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tops_1 @ X30 @ X31 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X14: $i] :
      ( ( k2_subset_1 @ X14 )
      = ( k3_subset_1 @ X14 @ ( k1_subset_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ! [X14: $i] :
      ( X14
      = ( k3_subset_1 @ X14 @ ( k1_subset_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v2_tops_1 @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_tops_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['30','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('48',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_subset_1 @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('53',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X14: $i] :
      ( X14
      = ( k3_subset_1 @ X14 @ ( k1_subset_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('59',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('60',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('63',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('64',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_subset_1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_subset_1 @ X1 ) )
      | ( X0
        = ( k1_subset_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( X1
        = ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = ( k1_subset_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('71',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_subset_1 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_tops_1 @ X1 @ ( k1_subset_1 @ X0 ) ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','75'])).

thf('77',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','76'])).

thf('78',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ X2 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( X0 = k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) )
        | ( X0 = k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','83'])).

thf('85',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['30','45'])).

thf('90',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('91',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('92',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('96',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('97',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('99',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('102',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('104',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('105',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,
    ( ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X13 @ ( k3_subset_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('113',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['30','45'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('116',plain,(
    ! [X7: $i] :
      ( ( k1_subset_1 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('117',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('119',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('120',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['123','124'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('126',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('129',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('130',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ k1_xboole_0 ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['117','134'])).

thf('136',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('137',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('139',plain,
    ( ( ( k1_tops_1 @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ( k1_tops_1 @ sk_A @ ( k1_subset_1 @ X0 ) )
        = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['116','139'])).

thf('141',plain,
    ( ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('148',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','146','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ( v2_tops_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('151',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','146','147'])).

thf('156',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('157',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','146','147'])).

thf('159',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','146','147'])).

thf('161',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_pre_topc @ X29 @ X28 )
       != ( k2_struct_0 @ X29 ) )
      | ( v1_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('162',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( v1_tops_1 @ X0 @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
         != ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['159','164'])).

thf('166',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('167',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','146','147'])).

thf('168',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','146','147'])).

thf('169',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['165','169'])).

thf('171',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','171'])).

thf('173',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('174',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','87','88','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fcJSAuM43r
% 0.12/0.35  % Computer   : n020.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 20:37:07 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.70/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.91  % Solved by: fo/fo7.sh
% 0.70/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.91  % done 1510 iterations in 0.450s
% 0.70/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.91  % SZS output start Refutation
% 0.70/0.91  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.70/0.91  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.70/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.91  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.70/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.91  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.70/0.91  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.70/0.91  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.70/0.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.91  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.70/0.91  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.70/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.91  thf(t84_tops_1, conjecture,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.91           ( ( v2_tops_1 @ B @ A ) <=>
% 0.70/0.91             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.70/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.91    (~( ![A:$i]:
% 0.70/0.91        ( ( l1_pre_topc @ A ) =>
% 0.70/0.91          ( ![B:$i]:
% 0.70/0.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.91              ( ( v2_tops_1 @ B @ A ) <=>
% 0.70/0.91                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.70/0.91    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.70/0.91  thf('0', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.70/0.91        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('1', plain,
% 0.70/0.91      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.70/0.91       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.70/0.91      inference('split', [status(esa)], ['0'])).
% 0.70/0.91  thf(d10_xboole_0, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.91  thf('2', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.70/0.91      inference('simplify', [status(thm)], ['2'])).
% 0.70/0.91  thf('4', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('5', plain,
% 0.70/0.91      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('split', [status(esa)], ['4'])).
% 0.70/0.91  thf('6', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(d4_tops_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.91           ( ( v2_tops_1 @ B @ A ) <=>
% 0.70/0.91             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.70/0.91  thf('7', plain,
% 0.70/0.91      (![X30 : $i, X31 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.70/0.91          | ~ (v2_tops_1 @ X30 @ X31)
% 0.70/0.91          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 0.70/0.91          | ~ (l1_pre_topc @ X31))),
% 0.70/0.91      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.70/0.91  thf('8', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.91        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.70/0.91        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['6', '7'])).
% 0.70/0.91  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('10', plain,
% 0.70/0.91      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.70/0.91        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.70/0.91      inference('demod', [status(thm)], ['8', '9'])).
% 0.70/0.91  thf('11', plain,
% 0.70/0.91      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.70/0.91         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['5', '10'])).
% 0.70/0.91  thf('12', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(dt_k3_subset_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.91       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.70/0.91  thf('13', plain,
% 0.70/0.91      (![X10 : $i, X11 : $i]:
% 0.70/0.91         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 0.70/0.91          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.70/0.91  thf('14', plain,
% 0.70/0.91      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.70/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.91  thf(d3_tops_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.91           ( ( v1_tops_1 @ B @ A ) <=>
% 0.70/0.91             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.70/0.91  thf('15', plain,
% 0.70/0.91      (![X28 : $i, X29 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.70/0.91          | ~ (v1_tops_1 @ X28 @ X29)
% 0.70/0.91          | ((k2_pre_topc @ X29 @ X28) = (k2_struct_0 @ X29))
% 0.70/0.91          | ~ (l1_pre_topc @ X29))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.70/0.91  thf('16', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.91        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.70/0.91            = (k2_struct_0 @ sk_A))
% 0.70/0.91        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['14', '15'])).
% 0.70/0.91  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('18', plain,
% 0.70/0.91      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.70/0.91          = (k2_struct_0 @ sk_A))
% 0.70/0.91        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.70/0.91      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.91  thf('19', plain,
% 0.70/0.91      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.70/0.91          = (k2_struct_0 @ sk_A)))
% 0.70/0.91         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['11', '18'])).
% 0.70/0.91  thf('20', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(d1_tops_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.91           ( ( k1_tops_1 @ A @ B ) =
% 0.70/0.91             ( k3_subset_1 @
% 0.70/0.91               ( u1_struct_0 @ A ) @ 
% 0.70/0.91               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.70/0.91  thf('21', plain,
% 0.70/0.91      (![X26 : $i, X27 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.70/0.91          | ((k1_tops_1 @ X27 @ X26)
% 0.70/0.91              = (k3_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.70/0.91                 (k2_pre_topc @ X27 @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26))))
% 0.70/0.91          | ~ (l1_pre_topc @ X27))),
% 0.70/0.91      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.70/0.91  thf('22', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.91        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.70/0.91            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.91               (k2_pre_topc @ sk_A @ 
% 0.70/0.91                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.70/0.91      inference('sup-', [status(thm)], ['20', '21'])).
% 0.70/0.91  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('24', plain,
% 0.70/0.91      (((k1_tops_1 @ sk_A @ sk_B)
% 0.70/0.91         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.91            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.70/0.91      inference('demod', [status(thm)], ['22', '23'])).
% 0.70/0.91  thf('25', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.70/0.91          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.70/0.91         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('sup+', [status(thm)], ['19', '24'])).
% 0.70/0.91  thf(dt_k2_subset_1, axiom,
% 0.70/0.91    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.70/0.91  thf('26', plain,
% 0.70/0.91      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.70/0.91  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.70/0.91  thf('27', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.70/0.91      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.70/0.91  thf('28', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.70/0.91      inference('demod', [status(thm)], ['26', '27'])).
% 0.70/0.91  thf('29', plain,
% 0.70/0.91      (![X28 : $i, X29 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.70/0.91          | ~ (v1_tops_1 @ X28 @ X29)
% 0.70/0.91          | ((k2_pre_topc @ X29 @ X28) = (k2_struct_0 @ X29))
% 0.70/0.91          | ~ (l1_pre_topc @ X29))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.70/0.91  thf('30', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.70/0.91          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['28', '29'])).
% 0.70/0.91  thf(t4_subset_1, axiom,
% 0.70/0.91    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.70/0.91  thf('31', plain,
% 0.70/0.91      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.70/0.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.91  thf('32', plain,
% 0.70/0.91      (![X30 : $i, X31 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.70/0.91          | ~ (v2_tops_1 @ X30 @ X31)
% 0.70/0.91          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 0.70/0.91          | ~ (l1_pre_topc @ X31))),
% 0.70/0.91      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.70/0.91  thf('33', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0)
% 0.70/0.91          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['31', '32'])).
% 0.70/0.91  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.91  thf('34', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf(t22_subset_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.70/0.91  thf('35', plain,
% 0.70/0.91      (![X14 : $i]:
% 0.70/0.91         ((k2_subset_1 @ X14) = (k3_subset_1 @ X14 @ (k1_subset_1 @ X14)))),
% 0.70/0.91      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.70/0.91  thf('36', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.70/0.91      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.70/0.91  thf('37', plain,
% 0.70/0.91      (![X14 : $i]: ((X14) = (k3_subset_1 @ X14 @ (k1_subset_1 @ X14)))),
% 0.70/0.91      inference('demod', [status(thm)], ['35', '36'])).
% 0.70/0.91  thf('38', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.70/0.91      inference('sup+', [status(thm)], ['34', '37'])).
% 0.70/0.91  thf('39', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.70/0.91          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.70/0.91      inference('demod', [status(thm)], ['33', '38'])).
% 0.70/0.91  thf('40', plain,
% 0.70/0.91      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.70/0.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.91  thf(cc2_tops_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.91           ( ( v1_xboole_0 @ B ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.70/0.91  thf('41', plain,
% 0.70/0.91      (![X24 : $i, X25 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.70/0.91          | (v2_tops_1 @ X24 @ X25)
% 0.70/0.91          | ~ (v1_xboole_0 @ X24)
% 0.70/0.91          | ~ (l1_pre_topc @ X25))),
% 0.70/0.91      inference('cnf', [status(esa)], [cc2_tops_1])).
% 0.70/0.91  thf('42', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.91          | (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['40', '41'])).
% 0.70/0.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.70/0.91  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.91  thf('44', plain,
% 0.70/0.91      (![X0 : $i]: (~ (l1_pre_topc @ X0) | (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.70/0.91      inference('demod', [status(thm)], ['42', '43'])).
% 0.70/0.91  thf('45', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('clc', [status(thm)], ['39', '44'])).
% 0.70/0.91  thf('46', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('clc', [status(thm)], ['30', '45'])).
% 0.70/0.91  thf('47', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf('48', plain,
% 0.70/0.91      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.70/0.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.91  thf('49', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.70/0.91      inference('sup+', [status(thm)], ['47', '48'])).
% 0.70/0.91  thf('50', plain,
% 0.70/0.91      (![X26 : $i, X27 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.70/0.91          | ((k1_tops_1 @ X27 @ X26)
% 0.70/0.91              = (k3_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.70/0.91                 (k2_pre_topc @ X27 @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26))))
% 0.70/0.91          | ~ (l1_pre_topc @ X27))),
% 0.70/0.91      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.70/0.91  thf('51', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ((k1_tops_1 @ X0 @ (k1_subset_1 @ X1))
% 0.70/0.91              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91                 (k2_pre_topc @ X0 @ 
% 0.70/0.91                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (k1_subset_1 @ X1))))))),
% 0.70/0.91      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.91  thf('52', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf('53', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf('54', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 0.70/0.91      inference('sup+', [status(thm)], ['52', '53'])).
% 0.70/0.91  thf('55', plain,
% 0.70/0.91      (![X14 : $i]: ((X14) = (k3_subset_1 @ X14 @ (k1_subset_1 @ X14)))),
% 0.70/0.91      inference('demod', [status(thm)], ['35', '36'])).
% 0.70/0.91  thf('56', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 0.70/0.91      inference('sup+', [status(thm)], ['54', '55'])).
% 0.70/0.91  thf('57', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ((k1_tops_1 @ X0 @ (k1_subset_1 @ X1))
% 0.70/0.91              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91                 (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 0.70/0.91      inference('demod', [status(thm)], ['51', '56'])).
% 0.70/0.91  thf('58', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf('59', plain,
% 0.70/0.91      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.70/0.91      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.91  thf(t44_tops_1, axiom,
% 0.70/0.91    (![A:$i]:
% 0.70/0.91     ( ( l1_pre_topc @ A ) =>
% 0.70/0.91       ( ![B:$i]:
% 0.70/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.91           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.70/0.91  thf('60', plain,
% 0.70/0.91      (![X32 : $i, X33 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.70/0.91          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 0.70/0.91          | ~ (l1_pre_topc @ X33))),
% 0.70/0.91      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.70/0.91  thf('61', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['59', '60'])).
% 0.70/0.91  thf('62', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf('63', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.70/0.91  thf('64', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.70/0.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.91  thf('65', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]: (r1_tarski @ (k1_subset_1 @ X0) @ X1)),
% 0.70/0.91      inference('sup+', [status(thm)], ['63', '64'])).
% 0.70/0.91  thf('66', plain,
% 0.70/0.91      (![X0 : $i, X2 : $i]:
% 0.70/0.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('67', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X0 @ (k1_subset_1 @ X1)) | ((X0) = (k1_subset_1 @ X1)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.70/0.91  thf('68', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X1 @ k1_xboole_0) | ((X1) = (k1_subset_1 @ X0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['62', '67'])).
% 0.70/0.91  thf('69', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_subset_1 @ X1)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['61', '68'])).
% 0.70/0.91  thf('70', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf('71', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.70/0.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.91  thf('72', plain,
% 0.70/0.91      (![X0 : $i, X2 : $i]:
% 0.70/0.91         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.70/0.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.91  thf('73', plain,
% 0.70/0.91      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['71', '72'])).
% 0.70/0.91  thf('74', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X1 @ (k1_subset_1 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['70', '73'])).
% 0.70/0.91  thf('75', plain,
% 0.70/0.91      (![X0 : $i, X2 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X2 @ (k1_tops_1 @ X0 @ k1_xboole_0))
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ((X2) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['69', '74'])).
% 0.70/0.91  thf('76', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X2 @ (k1_tops_1 @ X1 @ (k1_subset_1 @ X0)))
% 0.70/0.91          | ((X2) = (k1_xboole_0))
% 0.70/0.91          | ~ (l1_pre_topc @ X1))),
% 0.70/0.91      inference('sup-', [status(thm)], ['58', '75'])).
% 0.70/0.91  thf('77', plain,
% 0.70/0.91      (![X0 : $i, X2 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X2 @ 
% 0.70/0.91             (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91              (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ((X2) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['57', '76'])).
% 0.70/0.91  thf('78', plain,
% 0.70/0.91      (![X0 : $i, X2 : $i]:
% 0.70/0.91         (((X2) = (k1_xboole_0))
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (r1_tarski @ X2 @ 
% 0.70/0.91               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91                (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 0.70/0.91      inference('simplify', [status(thm)], ['77'])).
% 0.70/0.91  thf('79', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X1 @ 
% 0.70/0.91             (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ((X1) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['46', '78'])).
% 0.70/0.91  thf('80', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (((X1) = (k1_xboole_0))
% 0.70/0.91          | ~ (l1_pre_topc @ X0)
% 0.70/0.91          | ~ (r1_tarski @ X1 @ 
% 0.70/0.91               (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))))),
% 0.70/0.91      inference('simplify', [status(thm)], ['79'])).
% 0.70/0.91  thf('81', plain,
% 0.70/0.91      ((![X0 : $i]:
% 0.70/0.91          (~ (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.70/0.91           | ~ (l1_pre_topc @ sk_A)
% 0.70/0.91           | ((X0) = (k1_xboole_0))))
% 0.70/0.91         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['25', '80'])).
% 0.70/0.91  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('83', plain,
% 0.70/0.91      ((![X0 : $i]:
% 0.70/0.91          (~ (r1_tarski @ X0 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.70/0.91           | ((X0) = (k1_xboole_0))))
% 0.70/0.91         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('demod', [status(thm)], ['81', '82'])).
% 0.70/0.91  thf('84', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.70/0.91         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['3', '83'])).
% 0.70/0.91  thf('85', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.70/0.91         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('split', [status(esa)], ['0'])).
% 0.70/0.91  thf('86', plain,
% 0.70/0.91      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.70/0.91         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.70/0.91             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.70/0.91  thf('87', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.70/0.91       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.70/0.91      inference('simplify', [status(thm)], ['86'])).
% 0.70/0.91  thf('88', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.70/0.91       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.70/0.91      inference('split', [status(esa)], ['4'])).
% 0.70/0.91  thf('89', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('clc', [status(thm)], ['30', '45'])).
% 0.70/0.91  thf('90', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('split', [status(esa)], ['4'])).
% 0.70/0.91  thf('91', plain,
% 0.70/0.91      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.70/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.91  thf(dt_k2_pre_topc, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( ( l1_pre_topc @ A ) & 
% 0.70/0.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.70/0.91       ( m1_subset_1 @
% 0.70/0.91         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.70/0.91  thf('92', plain,
% 0.70/0.91      (![X22 : $i, X23 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X22)
% 0.70/0.91          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.70/0.91          | (m1_subset_1 @ (k2_pre_topc @ X22 @ X23) @ 
% 0.70/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.70/0.91  thf('93', plain,
% 0.70/0.91      (((m1_subset_1 @ 
% 0.70/0.91         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.70/0.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['91', '92'])).
% 0.70/0.91  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('95', plain,
% 0.70/0.91      ((m1_subset_1 @ 
% 0.70/0.91        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.70/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('demod', [status(thm)], ['93', '94'])).
% 0.70/0.91  thf(involutiveness_k3_subset_1, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.91       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.70/0.91  thf('96', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i]:
% 0.70/0.91         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.70/0.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.70/0.91      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.70/0.91  thf('97', plain,
% 0.70/0.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.91         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.91          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.70/0.91         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['95', '96'])).
% 0.70/0.91  thf('98', plain,
% 0.70/0.91      (((k1_tops_1 @ sk_A @ sk_B)
% 0.70/0.91         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.91            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.70/0.91      inference('demod', [status(thm)], ['22', '23'])).
% 0.70/0.91  thf('99', plain,
% 0.70/0.91      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.70/0.91         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.70/0.91      inference('demod', [status(thm)], ['97', '98'])).
% 0.70/0.91  thf('100', plain,
% 0.70/0.91      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.70/0.91          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup+', [status(thm)], ['90', '99'])).
% 0.70/0.91  thf('101', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.70/0.91      inference('sup+', [status(thm)], ['34', '37'])).
% 0.70/0.91  thf('102', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_A)
% 0.70/0.91          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['100', '101'])).
% 0.70/0.91  thf('103', plain,
% 0.70/0.91      ((m1_subset_1 @ 
% 0.70/0.91        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.70/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('demod', [status(thm)], ['93', '94'])).
% 0.70/0.91  thf('104', plain,
% 0.70/0.91      (![X22 : $i, X23 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X22)
% 0.70/0.91          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.70/0.91          | (m1_subset_1 @ (k2_pre_topc @ X22 @ X23) @ 
% 0.70/0.91             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.70/0.91      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.70/0.91  thf('105', plain,
% 0.70/0.91      (((m1_subset_1 @ 
% 0.70/0.91         (k2_pre_topc @ sk_A @ 
% 0.70/0.91          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.70/0.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.91        | ~ (l1_pre_topc @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['103', '104'])).
% 0.70/0.91  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('107', plain,
% 0.70/0.91      ((m1_subset_1 @ 
% 0.70/0.91        (k2_pre_topc @ sk_A @ 
% 0.70/0.91         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.70/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('demod', [status(thm)], ['105', '106'])).
% 0.70/0.91  thf('108', plain,
% 0.70/0.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 0.70/0.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup+', [status(thm)], ['102', '107'])).
% 0.70/0.91  thf('109', plain,
% 0.70/0.91      ((((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.70/0.91          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.91         | ~ (l1_pre_topc @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup+', [status(thm)], ['89', '108'])).
% 0.70/0.91  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('111', plain,
% 0.70/0.91      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.70/0.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['109', '110'])).
% 0.70/0.91  thf('112', plain,
% 0.70/0.91      (![X12 : $i, X13 : $i]:
% 0.70/0.91         (((k3_subset_1 @ X13 @ (k3_subset_1 @ X13 @ X12)) = (X12))
% 0.70/0.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.70/0.91      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.70/0.91  thf('113', plain,
% 0.70/0.91      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.91          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.70/0.91          = (k2_struct_0 @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup-', [status(thm)], ['111', '112'])).
% 0.70/0.91  thf('114', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.70/0.91          | ~ (l1_pre_topc @ X0))),
% 0.70/0.91      inference('clc', [status(thm)], ['30', '45'])).
% 0.70/0.91  thf('115', plain,
% 0.70/0.91      (![X0 : $i, X1 : $i]:
% 0.70/0.91         (~ (l1_pre_topc @ X0)
% 0.70/0.91          | ((k1_tops_1 @ X0 @ (k1_subset_1 @ X1))
% 0.70/0.91              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.91                 (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 0.70/0.91      inference('demod', [status(thm)], ['51', '56'])).
% 0.70/0.91  thf('116', plain, (![X7 : $i]: ((k1_subset_1 @ X7) = (k1_xboole_0))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.91  thf('117', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('split', [status(esa)], ['4'])).
% 0.70/0.91  thf('118', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf(t3_subset, axiom,
% 0.70/0.91    (![A:$i,B:$i]:
% 0.70/0.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.91  thf('119', plain,
% 0.70/0.91      (![X16 : $i, X17 : $i]:
% 0.70/0.91         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.70/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.91  thf('120', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['118', '119'])).
% 0.70/0.91  thf('121', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('122', plain,
% 0.70/0.91      (![X32 : $i, X33 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.70/0.91          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 0.70/0.91          | ~ (l1_pre_topc @ X33))),
% 0.70/0.91      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.70/0.91  thf('123', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.70/0.91      inference('sup-', [status(thm)], ['121', '122'])).
% 0.70/0.91  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('125', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.70/0.91      inference('demod', [status(thm)], ['123', '124'])).
% 0.70/0.91  thf(t1_xboole_1, axiom,
% 0.70/0.91    (![A:$i,B:$i,C:$i]:
% 0.70/0.91     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.70/0.91       ( r1_tarski @ A @ C ) ))).
% 0.70/0.91  thf('126', plain,
% 0.70/0.91      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.70/0.91         (~ (r1_tarski @ X3 @ X4)
% 0.70/0.91          | ~ (r1_tarski @ X4 @ X5)
% 0.70/0.91          | (r1_tarski @ X3 @ X5))),
% 0.70/0.91      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.70/0.91  thf('127', plain,
% 0.70/0.91      (![X0 : $i]:
% 0.70/0.91         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.70/0.91          | ~ (r1_tarski @ sk_B @ X0))),
% 0.70/0.91      inference('sup-', [status(thm)], ['125', '126'])).
% 0.70/0.91  thf('128', plain,
% 0.70/0.91      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['120', '127'])).
% 0.70/0.91  thf('129', plain,
% 0.70/0.91      (![X16 : $i, X18 : $i]:
% 0.70/0.91         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.70/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.91  thf('130', plain,
% 0.70/0.91      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.70/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['128', '129'])).
% 0.70/0.91  thf('131', plain,
% 0.70/0.91      (![X32 : $i, X33 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.70/0.91          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 0.70/0.91          | ~ (l1_pre_topc @ X33))),
% 0.70/0.91      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.70/0.91  thf('132', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.91        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.70/0.91           (k1_tops_1 @ sk_A @ sk_B)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['130', '131'])).
% 0.70/0.91  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('134', plain,
% 0.70/0.91      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.70/0.91        (k1_tops_1 @ sk_A @ sk_B))),
% 0.70/0.91      inference('demod', [status(thm)], ['132', '133'])).
% 0.70/0.91  thf('135', plain,
% 0.70/0.91      (((r1_tarski @ (k1_tops_1 @ sk_A @ k1_xboole_0) @ 
% 0.70/0.91         (k1_tops_1 @ sk_A @ sk_B)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup+', [status(thm)], ['117', '134'])).
% 0.70/0.91  thf('136', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('split', [status(esa)], ['4'])).
% 0.70/0.91  thf('137', plain,
% 0.70/0.91      (((r1_tarski @ (k1_tops_1 @ sk_A @ k1_xboole_0) @ k1_xboole_0))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['135', '136'])).
% 0.70/0.91  thf('138', plain,
% 0.70/0.91      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['71', '72'])).
% 0.70/0.91  thf('139', plain,
% 0.70/0.91      ((((k1_tops_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup-', [status(thm)], ['137', '138'])).
% 0.70/0.91  thf('140', plain,
% 0.70/0.91      ((![X0 : $i]: ((k1_tops_1 @ sk_A @ (k1_subset_1 @ X0)) = (k1_xboole_0)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup+', [status(thm)], ['116', '139'])).
% 0.70/0.91  thf('141', plain,
% 0.70/0.91      (((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.91           (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))) = (k1_xboole_0))
% 0.70/0.91         | ~ (l1_pre_topc @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup+', [status(thm)], ['115', '140'])).
% 0.70/0.91  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('143', plain,
% 0.70/0.91      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.70/0.91          (k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A))) = (k1_xboole_0)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['141', '142'])).
% 0.70/0.91  thf('144', plain,
% 0.70/0.91      (((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.70/0.91           = (k1_xboole_0))
% 0.70/0.91         | ~ (l1_pre_topc @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup+', [status(thm)], ['114', '143'])).
% 0.70/0.91  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('146', plain,
% 0.70/0.91      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.70/0.91          = (k1_xboole_0)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['144', '145'])).
% 0.70/0.91  thf('147', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.70/0.91      inference('sup+', [status(thm)], ['34', '37'])).
% 0.70/0.91  thf('148', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['113', '146', '147'])).
% 0.70/0.91  thf('149', plain,
% 0.70/0.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('150', plain,
% 0.70/0.91      (![X30 : $i, X31 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.70/0.91          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 0.70/0.91          | (v2_tops_1 @ X30 @ X31)
% 0.70/0.91          | ~ (l1_pre_topc @ X31))),
% 0.70/0.91      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.70/0.91  thf('151', plain,
% 0.70/0.91      ((~ (l1_pre_topc @ sk_A)
% 0.70/0.91        | (v2_tops_1 @ sk_B @ sk_A)
% 0.70/0.91        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['149', '150'])).
% 0.70/0.91  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('153', plain,
% 0.70/0.91      (((v2_tops_1 @ sk_B @ sk_A)
% 0.70/0.91        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.70/0.91      inference('demod', [status(thm)], ['151', '152'])).
% 0.70/0.91  thf('154', plain,
% 0.70/0.91      (((~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.70/0.91         | (v2_tops_1 @ sk_B @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup-', [status(thm)], ['148', '153'])).
% 0.70/0.91  thf('155', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['113', '146', '147'])).
% 0.70/0.91  thf('156', plain,
% 0.70/0.91      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.70/0.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.91      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.91  thf('157', plain,
% 0.70/0.91      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.70/0.91         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup+', [status(thm)], ['155', '156'])).
% 0.70/0.91  thf('158', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['113', '146', '147'])).
% 0.70/0.91  thf('159', plain,
% 0.70/0.91      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.70/0.91         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['157', '158'])).
% 0.70/0.91  thf('160', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['113', '146', '147'])).
% 0.70/0.91  thf('161', plain,
% 0.70/0.91      (![X28 : $i, X29 : $i]:
% 0.70/0.91         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.70/0.91          | ((k2_pre_topc @ X29 @ X28) != (k2_struct_0 @ X29))
% 0.70/0.91          | (v1_tops_1 @ X28 @ X29)
% 0.70/0.91          | ~ (l1_pre_topc @ X29))),
% 0.70/0.91      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.70/0.91  thf('162', plain,
% 0.70/0.91      ((![X0 : $i]:
% 0.70/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.70/0.91           | ~ (l1_pre_topc @ sk_A)
% 0.70/0.91           | (v1_tops_1 @ X0 @ sk_A)
% 0.70/0.91           | ((k2_pre_topc @ sk_A @ X0) != (k2_struct_0 @ sk_A))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup-', [status(thm)], ['160', '161'])).
% 0.70/0.91  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.91  thf('164', plain,
% 0.70/0.91      ((![X0 : $i]:
% 0.70/0.91          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.70/0.91           | (v1_tops_1 @ X0 @ sk_A)
% 0.70/0.91           | ((k2_pre_topc @ sk_A @ X0) != (k2_struct_0 @ sk_A))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['162', '163'])).
% 0.70/0.91  thf('165', plain,
% 0.70/0.91      (((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.70/0.91           != (k2_struct_0 @ sk_A))
% 0.70/0.91         | (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('sup-', [status(thm)], ['159', '164'])).
% 0.70/0.91  thf('166', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_A)
% 0.70/0.91          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['100', '101'])).
% 0.70/0.91  thf('167', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['113', '146', '147'])).
% 0.70/0.91  thf('168', plain,
% 0.70/0.91      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['113', '146', '147'])).
% 0.70/0.91  thf('169', plain,
% 0.70/0.91      ((((k2_struct_0 @ sk_A)
% 0.70/0.91          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.70/0.91  thf('170', plain,
% 0.70/0.91      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.70/0.91         | (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['165', '169'])).
% 0.70/0.91  thf('171', plain,
% 0.70/0.91      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('simplify', [status(thm)], ['170'])).
% 0.70/0.91  thf('172', plain,
% 0.70/0.91      (((v2_tops_1 @ sk_B @ sk_A))
% 0.70/0.91         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.70/0.91      inference('demod', [status(thm)], ['154', '171'])).
% 0.70/0.91  thf('173', plain,
% 0.70/0.91      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.70/0.91      inference('split', [status(esa)], ['0'])).
% 0.70/0.91  thf('174', plain,
% 0.70/0.91      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.70/0.91       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.70/0.91      inference('sup-', [status(thm)], ['172', '173'])).
% 0.70/0.91  thf('175', plain, ($false),
% 0.70/0.91      inference('sat_resolution*', [status(thm)], ['1', '87', '88', '174'])).
% 0.70/0.91  
% 0.70/0.91  % SZS output end Refutation
% 0.70/0.91  
% 0.70/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
