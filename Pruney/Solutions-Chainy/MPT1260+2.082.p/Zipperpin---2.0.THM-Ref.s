%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bd3Y1n4jA8

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:36 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 577 expanded)
%              Number of leaves         :   29 ( 173 expanded)
%              Depth                    :   21
%              Number of atoms          : 1641 (8266 expanded)
%              Number of equality atoms :  101 ( 404 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k1_tops_1 @ X37 @ X36 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ X26 @ ( k2_pre_topc @ X27 @ X26 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','25'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('28',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X16 @ X14 )
        = ( k9_subset_1 @ X15 @ X16 @ ( k3_subset_1 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      | ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('42',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('46',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('49',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('51',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','51'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('58',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(split,[status(esa)],['57'])).

thf('61',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ~ ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( v3_pre_topc @ X33 @ X32 )
        | ( ( k1_tops_1 @ X32 @ X33 )
          = X33 ) )
    | ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(split,[status(esa)],['57'])).

thf('66',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 ) ) ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X33 @ X32 )
      | ( ( k1_tops_1 @ X32 @ X33 )
        = X33 ) ) ),
    inference(simpl_trail,[status(thm)],['58','66'])).

thf('68',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','70'])).

thf('72',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','25'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('76',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['34'])).

thf('80',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['54','78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['52','80'])).

thf('82',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','81'])).

thf('83',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['54','78','79'])).

thf('84',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      | ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','84'])).

thf('86',plain,
    ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['14','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('88',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('91',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X7 @ X6 @ X6 )
        = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('92',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ X2 )
      = X2 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['86','89','92'])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['7','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('97',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('100',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('102',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['97','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('104',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k1_tops_1 @ X35 @ X34 )
       != X34 )
      | ( v3_pre_topc @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('105',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 )
        | ( ( k1_tops_1 @ X35 @ X34 )
         != X34 )
        | ( v3_pre_topc @ X34 @ X35 ) )
   <= ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 )
        | ( ( k1_tops_1 @ X35 @ X34 )
         != X34 )
        | ( v3_pre_topc @ X34 @ X35 ) ) ),
    inference(split,[status(esa)],['104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(split,[status(esa)],['104'])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ~ ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ! [X34: $i,X35: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
        | ~ ( l1_pre_topc @ X35 )
        | ~ ( v2_pre_topc @ X35 )
        | ( ( k1_tops_1 @ X35 @ X34 )
         != X34 )
        | ( v3_pre_topc @ X34 @ X35 ) )
    | ! [X32: $i,X33: $i] :
        ( ~ ( l1_pre_topc @ X32 )
        | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) ) ),
    inference(split,[status(esa)],['104'])).

thf('112',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( ( k1_tops_1 @ X35 @ X34 )
       != X34 )
      | ( v3_pre_topc @ X34 @ X35 ) ) ),
    inference('sat_resolution*',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( ( k1_tops_1 @ X35 @ X34 )
       != X34 )
      | ( v3_pre_topc @ X34 @ X35 ) ) ),
    inference(simpl_trail,[status(thm)],['105','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
       != ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','113'])).

thf('115',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','114'])).

thf('116',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['97','100','101'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['97','100','101'])).

thf('120',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('122',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['54','78'])).

thf('123',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['121','122'])).

thf('124',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['120','123'])).

thf('125',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['94','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bd3Y1n4jA8
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.90/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.09  % Solved by: fo/fo7.sh
% 0.90/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.09  % done 1399 iterations in 0.631s
% 0.90/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.09  % SZS output start Refutation
% 0.90/1.09  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.90/1.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.09  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.90/1.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.09  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.90/1.09  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.09  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.90/1.09  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.90/1.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.09  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.90/1.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.09  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.90/1.09  thf(t76_tops_1, conjecture,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( ( v3_pre_topc @ B @ A ) <=>
% 0.90/1.09             ( ( k2_tops_1 @ A @ B ) =
% 0.90/1.09               ( k7_subset_1 @
% 0.90/1.09                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.90/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.09    (~( ![A:$i]:
% 0.90/1.09        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.09          ( ![B:$i]:
% 0.90/1.09            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09              ( ( v3_pre_topc @ B @ A ) <=>
% 0.90/1.09                ( ( k2_tops_1 @ A @ B ) =
% 0.90/1.09                  ( k7_subset_1 @
% 0.90/1.09                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.90/1.09    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.90/1.09  thf('0', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t74_tops_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_pre_topc @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( ( k1_tops_1 @ A @ B ) =
% 0.90/1.09             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.09  thf('1', plain,
% 0.90/1.09      (![X36 : $i, X37 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.90/1.09          | ((k1_tops_1 @ X37 @ X36)
% 0.90/1.09              = (k7_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.90/1.09                 (k2_tops_1 @ X37 @ X36)))
% 0.90/1.09          | ~ (l1_pre_topc @ X37))),
% 0.90/1.09      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.90/1.09  thf('2', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.09        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.90/1.09            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.09               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.09  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('4', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(redefinition_k7_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.90/1.09  thf('5', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.90/1.09          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.90/1.09  thf('6', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.90/1.09           = (k4_xboole_0 @ sk_B @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.09  thf('7', plain,
% 0.90/1.09      (((k1_tops_1 @ sk_A @ sk_B)
% 0.90/1.09         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['2', '3', '6'])).
% 0.90/1.09  thf('8', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t48_pre_topc, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_pre_topc @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.90/1.09  thf('9', plain,
% 0.90/1.09      (![X26 : $i, X27 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.90/1.09          | (r1_tarski @ X26 @ (k2_pre_topc @ X27 @ X26))
% 0.90/1.09          | ~ (l1_pre_topc @ X27))),
% 0.90/1.09      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.90/1.09  thf('10', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.09        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.09  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('12', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.09  thf(t3_subset, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.09  thf('13', plain,
% 0.90/1.09      (![X18 : $i, X20 : $i]:
% 0.90/1.09         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.09  thf('14', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.09  thf('15', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(l78_tops_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( l1_pre_topc @ A ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09           ( ( k2_tops_1 @ A @ B ) =
% 0.90/1.09             ( k7_subset_1 @
% 0.90/1.09               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.90/1.09               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.09  thf('16', plain,
% 0.90/1.09      (![X30 : $i, X31 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.90/1.09          | ((k2_tops_1 @ X31 @ X30)
% 0.90/1.09              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.90/1.09                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.90/1.09          | ~ (l1_pre_topc @ X31))),
% 0.90/1.09      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.90/1.09  thf('17', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.09        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['15', '16'])).
% 0.90/1.09  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('19', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(dt_k2_pre_topc, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( ( l1_pre_topc @ A ) & 
% 0.90/1.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.09       ( m1_subset_1 @
% 0.90/1.09         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.09  thf('20', plain,
% 0.90/1.09      (![X24 : $i, X25 : $i]:
% 0.90/1.09         (~ (l1_pre_topc @ X24)
% 0.90/1.09          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.90/1.09          | (m1_subset_1 @ (k2_pre_topc @ X24 @ X25) @ 
% 0.90/1.09             (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.90/1.09      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.90/1.09  thf('21', plain,
% 0.90/1.09      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.09        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['19', '20'])).
% 0.90/1.09  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('23', plain,
% 0.90/1.09      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('demod', [status(thm)], ['21', '22'])).
% 0.90/1.09  thf('24', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.90/1.09          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.90/1.09  thf('25', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.09  thf('26', plain,
% 0.90/1.09      (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['17', '18', '25'])).
% 0.90/1.09  thf(t36_xboole_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.09  thf('27', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.90/1.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.09  thf('28', plain,
% 0.90/1.09      (![X18 : $i, X20 : $i]:
% 0.90/1.09         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.90/1.09      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.09  thf('29', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.09  thf('30', plain,
% 0.90/1.09      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.09        (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.90/1.09      inference('sup+', [status(thm)], ['26', '29'])).
% 0.90/1.09  thf(t32_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ![C:$i]:
% 0.90/1.09         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.90/1.09             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.90/1.09  thf('31', plain,
% 0.90/1.09      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.90/1.09          | ((k7_subset_1 @ X15 @ X16 @ X14)
% 0.90/1.09              = (k9_subset_1 @ X15 @ X16 @ (k3_subset_1 @ X15 @ X14)))
% 0.90/1.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.90/1.09      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.90/1.09  thf('32', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.90/1.09          | ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ 
% 0.90/1.09              (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09              = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ 
% 0.90/1.09                 (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09                  (k2_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.09  thf('33', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.09  thf('34', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.90/1.09        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('35', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('split', [status(esa)], ['34'])).
% 0.90/1.09  thf('36', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['33', '35'])).
% 0.90/1.09  thf('37', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.09  thf(d5_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.90/1.09  thf('38', plain,
% 0.90/1.09      (![X2 : $i, X3 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.90/1.09          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.90/1.09  thf('39', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.90/1.09           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.09  thf('40', plain,
% 0.90/1.09      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09             (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['36', '39'])).
% 0.90/1.09  thf('41', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['33', '35'])).
% 0.90/1.09  thf('42', plain,
% 0.90/1.09      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09             (k2_tops_1 @ sk_A @ sk_B))))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('demod', [status(thm)], ['40', '41'])).
% 0.90/1.09  thf('43', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['33', '35'])).
% 0.90/1.09  thf('44', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.09  thf(involutiveness_k3_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.90/1.09  thf('45', plain,
% 0.90/1.09      (![X9 : $i, X10 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 0.90/1.09          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.90/1.09      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.90/1.09  thf('46', plain,
% 0.90/1.09      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.09  thf('47', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.09  thf('48', plain,
% 0.90/1.09      (![X2 : $i, X3 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.90/1.09          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.90/1.09  thf('49', plain,
% 0.90/1.09      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.90/1.09         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['47', '48'])).
% 0.90/1.09  thf('50', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.90/1.09           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.09  thf('51', plain,
% 0.90/1.09      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['46', '49', '50'])).
% 0.90/1.09  thf('52', plain,
% 0.90/1.09      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('sup+', [status(thm)], ['43', '51'])).
% 0.90/1.09  thf('53', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.90/1.09        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('54', plain,
% 0.90/1.09      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.90/1.09       ~
% 0.90/1.09       (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.90/1.09      inference('split', [status(esa)], ['53'])).
% 0.90/1.09  thf('55', plain,
% 0.90/1.09      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('split', [status(esa)], ['34'])).
% 0.90/1.09  thf('56', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf(t55_tops_1, axiom,
% 0.90/1.09    (![A:$i]:
% 0.90/1.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.09       ( ![B:$i]:
% 0.90/1.09         ( ( l1_pre_topc @ B ) =>
% 0.90/1.09           ( ![C:$i]:
% 0.90/1.09             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.09               ( ![D:$i]:
% 0.90/1.09                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.90/1.09                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.90/1.09                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.90/1.09                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.90/1.09                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.90/1.09  thf('57', plain,
% 0.90/1.09      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.90/1.09         (~ (l1_pre_topc @ X32)
% 0.90/1.09          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.90/1.09          | ~ (v3_pre_topc @ X33 @ X32)
% 0.90/1.09          | ((k1_tops_1 @ X32 @ X33) = (X33))
% 0.90/1.09          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09          | ~ (l1_pre_topc @ X35)
% 0.90/1.09          | ~ (v2_pre_topc @ X35))),
% 0.90/1.09      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.90/1.09  thf('58', plain,
% 0.90/1.09      ((![X32 : $i, X33 : $i]:
% 0.90/1.09          (~ (l1_pre_topc @ X32)
% 0.90/1.09           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.90/1.09           | ~ (v3_pre_topc @ X33 @ X32)
% 0.90/1.09           | ((k1_tops_1 @ X32 @ X33) = (X33))))
% 0.90/1.09         <= ((![X32 : $i, X33 : $i]:
% 0.90/1.09                (~ (l1_pre_topc @ X32)
% 0.90/1.09                 | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.90/1.09                 | ~ (v3_pre_topc @ X33 @ X32)
% 0.90/1.09                 | ((k1_tops_1 @ X32 @ X33) = (X33)))))),
% 0.90/1.09      inference('split', [status(esa)], ['57'])).
% 0.90/1.09  thf('59', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('60', plain,
% 0.90/1.09      ((![X34 : $i, X35 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09           | ~ (l1_pre_topc @ X35)
% 0.90/1.09           | ~ (v2_pre_topc @ X35)))
% 0.90/1.09         <= ((![X34 : $i, X35 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09                 | ~ (l1_pre_topc @ X35)
% 0.90/1.09                 | ~ (v2_pre_topc @ X35))))),
% 0.90/1.09      inference('split', [status(esa)], ['57'])).
% 0.90/1.09  thf('61', plain,
% 0.90/1.09      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.90/1.09         <= ((![X34 : $i, X35 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09                 | ~ (l1_pre_topc @ X35)
% 0.90/1.09                 | ~ (v2_pre_topc @ X35))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.09  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('64', plain,
% 0.90/1.09      (~
% 0.90/1.09       (![X34 : $i, X35 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09           | ~ (l1_pre_topc @ X35)
% 0.90/1.09           | ~ (v2_pre_topc @ X35)))),
% 0.90/1.09      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.90/1.09  thf('65', plain,
% 0.90/1.09      ((![X32 : $i, X33 : $i]:
% 0.90/1.09          (~ (l1_pre_topc @ X32)
% 0.90/1.09           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.90/1.09           | ~ (v3_pre_topc @ X33 @ X32)
% 0.90/1.09           | ((k1_tops_1 @ X32 @ X33) = (X33)))) | 
% 0.90/1.09       (![X34 : $i, X35 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09           | ~ (l1_pre_topc @ X35)
% 0.90/1.09           | ~ (v2_pre_topc @ X35)))),
% 0.90/1.09      inference('split', [status(esa)], ['57'])).
% 0.90/1.09  thf('66', plain,
% 0.90/1.09      ((![X32 : $i, X33 : $i]:
% 0.90/1.09          (~ (l1_pre_topc @ X32)
% 0.90/1.09           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.90/1.09           | ~ (v3_pre_topc @ X33 @ X32)
% 0.90/1.09           | ((k1_tops_1 @ X32 @ X33) = (X33))))),
% 0.90/1.09      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.90/1.09  thf('67', plain,
% 0.90/1.09      (![X32 : $i, X33 : $i]:
% 0.90/1.09         (~ (l1_pre_topc @ X32)
% 0.90/1.09          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.90/1.09          | ~ (v3_pre_topc @ X33 @ X32)
% 0.90/1.09          | ((k1_tops_1 @ X32 @ X33) = (X33)))),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['58', '66'])).
% 0.90/1.09  thf('68', plain,
% 0.90/1.09      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.90/1.09        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.90/1.09        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['56', '67'])).
% 0.90/1.09  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('70', plain,
% 0.90/1.09      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['68', '69'])).
% 0.90/1.09  thf('71', plain,
% 0.90/1.09      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.90/1.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['55', '70'])).
% 0.90/1.09  thf('72', plain,
% 0.90/1.09      (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['17', '18', '25'])).
% 0.90/1.09  thf('73', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.90/1.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup+', [status(thm)], ['71', '72'])).
% 0.90/1.09  thf('74', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.09           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.09  thf('75', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.90/1.09         <= (~
% 0.90/1.09             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('split', [status(esa)], ['53'])).
% 0.90/1.09  thf('76', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.90/1.09         <= (~
% 0.90/1.09             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['74', '75'])).
% 0.90/1.09  thf('77', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.09         <= (~
% 0.90/1.09             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.90/1.09             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['73', '76'])).
% 0.90/1.09  thf('78', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.90/1.09       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('simplify', [status(thm)], ['77'])).
% 0.90/1.09  thf('79', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.90/1.09       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('split', [status(esa)], ['34'])).
% 0.90/1.09  thf('80', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.90/1.09      inference('sat_resolution*', [status(thm)], ['54', '78', '79'])).
% 0.90/1.09  thf('81', plain,
% 0.90/1.09      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09         = (sk_B))),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['52', '80'])).
% 0.90/1.09  thf('82', plain,
% 0.90/1.09      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09          = (sk_B)))
% 0.90/1.09         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.90/1.09      inference('demod', [status(thm)], ['42', '81'])).
% 0.90/1.09  thf('83', plain,
% 0.90/1.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.90/1.09      inference('sat_resolution*', [status(thm)], ['54', '78', '79'])).
% 0.90/1.09  thf('84', plain,
% 0.90/1.09      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09         = (sk_B))),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.90/1.09  thf('85', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.90/1.09          | ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ 
% 0.90/1.09              (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09              = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ sk_B)))),
% 0.90/1.09      inference('demod', [status(thm)], ['32', '84'])).
% 0.90/1.09  thf('86', plain,
% 0.90/1.09      (((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ 
% 0.90/1.09         (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.09         = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['14', '85'])).
% 0.90/1.09  thf('87', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.09  thf('88', plain,
% 0.90/1.09      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.90/1.09          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.90/1.09      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.90/1.09  thf('89', plain,
% 0.90/1.09      (![X0 : $i]:
% 0.90/1.09         ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ X0)
% 0.90/1.09           = (k4_xboole_0 @ sk_B @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['87', '88'])).
% 0.90/1.09  thf('90', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.09  thf(idempotence_k9_subset_1, axiom,
% 0.90/1.09    (![A:$i,B:$i,C:$i]:
% 0.90/1.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.09       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.90/1.09  thf('91', plain,
% 0.90/1.09      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.90/1.09         (((k9_subset_1 @ X7 @ X6 @ X6) = (X6))
% 0.90/1.09          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.90/1.09      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.90/1.09  thf('92', plain,
% 0.90/1.09      (![X0 : $i, X2 : $i]: ((k9_subset_1 @ X0 @ X2 @ X2) = (X2))),
% 0.90/1.09      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.09  thf('93', plain,
% 0.90/1.09      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['86', '89', '92'])).
% 0.90/1.09  thf('94', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.90/1.09      inference('sup+', [status(thm)], ['7', '93'])).
% 0.90/1.09  thf('95', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('96', plain,
% 0.90/1.09      (![X9 : $i, X10 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 0.90/1.09          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.90/1.09      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.90/1.09  thf('97', plain,
% 0.90/1.09      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['95', '96'])).
% 0.90/1.09  thf('98', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('99', plain,
% 0.90/1.09      (![X2 : $i, X3 : $i]:
% 0.90/1.09         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.90/1.09          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.90/1.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.90/1.09  thf('100', plain,
% 0.90/1.09      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.90/1.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.90/1.09      inference('sup-', [status(thm)], ['98', '99'])).
% 0.90/1.09  thf('101', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.90/1.09           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.90/1.09      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.09  thf('102', plain,
% 0.90/1.09      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['97', '100', '101'])).
% 0.90/1.09  thf('103', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.09  thf('104', plain,
% 0.90/1.09      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.90/1.09         (~ (l1_pre_topc @ X32)
% 0.90/1.09          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.90/1.09          | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.90/1.09          | (v3_pre_topc @ X34 @ X35)
% 0.90/1.09          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09          | ~ (l1_pre_topc @ X35)
% 0.90/1.09          | ~ (v2_pre_topc @ X35))),
% 0.90/1.09      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.90/1.09  thf('105', plain,
% 0.90/1.09      ((![X34 : $i, X35 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09           | ~ (l1_pre_topc @ X35)
% 0.90/1.09           | ~ (v2_pre_topc @ X35)
% 0.90/1.09           | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.90/1.09           | (v3_pre_topc @ X34 @ X35)))
% 0.90/1.09         <= ((![X34 : $i, X35 : $i]:
% 0.90/1.09                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09                 | ~ (l1_pre_topc @ X35)
% 0.90/1.09                 | ~ (v2_pre_topc @ X35)
% 0.90/1.09                 | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.90/1.09                 | (v3_pre_topc @ X34 @ X35))))),
% 0.90/1.09      inference('split', [status(esa)], ['104'])).
% 0.90/1.09  thf('106', plain,
% 0.90/1.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('107', plain,
% 0.90/1.09      ((![X32 : $i, X33 : $i]:
% 0.90/1.09          (~ (l1_pre_topc @ X32)
% 0.90/1.09           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))))
% 0.90/1.09         <= ((![X32 : $i, X33 : $i]:
% 0.90/1.09                (~ (l1_pre_topc @ X32)
% 0.90/1.09                 | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))))),
% 0.90/1.09      inference('split', [status(esa)], ['104'])).
% 0.90/1.09  thf('108', plain,
% 0.90/1.09      ((~ (l1_pre_topc @ sk_A))
% 0.90/1.09         <= ((![X32 : $i, X33 : $i]:
% 0.90/1.09                (~ (l1_pre_topc @ X32)
% 0.90/1.09                 | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))))),
% 0.90/1.09      inference('sup-', [status(thm)], ['106', '107'])).
% 0.90/1.09  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('110', plain,
% 0.90/1.09      (~
% 0.90/1.09       (![X32 : $i, X33 : $i]:
% 0.90/1.09          (~ (l1_pre_topc @ X32)
% 0.90/1.09           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))))),
% 0.90/1.09      inference('demod', [status(thm)], ['108', '109'])).
% 0.90/1.09  thf('111', plain,
% 0.90/1.09      ((![X34 : $i, X35 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09           | ~ (l1_pre_topc @ X35)
% 0.90/1.09           | ~ (v2_pre_topc @ X35)
% 0.90/1.09           | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.90/1.09           | (v3_pre_topc @ X34 @ X35))) | 
% 0.90/1.09       (![X32 : $i, X33 : $i]:
% 0.90/1.09          (~ (l1_pre_topc @ X32)
% 0.90/1.09           | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))))),
% 0.90/1.09      inference('split', [status(esa)], ['104'])).
% 0.90/1.09  thf('112', plain,
% 0.90/1.09      ((![X34 : $i, X35 : $i]:
% 0.90/1.09          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09           | ~ (l1_pre_topc @ X35)
% 0.90/1.09           | ~ (v2_pre_topc @ X35)
% 0.90/1.09           | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.90/1.09           | (v3_pre_topc @ X34 @ X35)))),
% 0.90/1.09      inference('sat_resolution*', [status(thm)], ['110', '111'])).
% 0.90/1.09  thf('113', plain,
% 0.90/1.09      (![X34 : $i, X35 : $i]:
% 0.90/1.09         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.90/1.09          | ~ (l1_pre_topc @ X35)
% 0.90/1.09          | ~ (v2_pre_topc @ X35)
% 0.90/1.09          | ((k1_tops_1 @ X35 @ X34) != (X34))
% 0.90/1.09          | (v3_pre_topc @ X34 @ X35))),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['105', '112'])).
% 0.90/1.09  thf('114', plain,
% 0.90/1.09      (![X0 : $i, X1 : $i]:
% 0.90/1.09         ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.90/1.09          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.90/1.09              != (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.90/1.09          | ~ (v2_pre_topc @ X0)
% 0.90/1.09          | ~ (l1_pre_topc @ X0))),
% 0.90/1.09      inference('sup-', [status(thm)], ['103', '113'])).
% 0.90/1.09  thf('115', plain,
% 0.90/1.09      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.90/1.09          != (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.90/1.09        | ~ (l1_pre_topc @ sk_A)
% 0.90/1.09        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.09        | (v3_pre_topc @ 
% 0.90/1.09           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.90/1.09           sk_A))),
% 0.90/1.09      inference('sup-', [status(thm)], ['102', '114'])).
% 0.90/1.09  thf('116', plain,
% 0.90/1.09      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['97', '100', '101'])).
% 0.90/1.09  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.09  thf('119', plain,
% 0.90/1.09      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.09         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.90/1.09      inference('demod', [status(thm)], ['97', '100', '101'])).
% 0.90/1.09  thf('120', plain,
% 0.90/1.09      ((((k1_tops_1 @ sk_A @ sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.90/1.09  thf('121', plain,
% 0.90/1.09      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.09      inference('split', [status(esa)], ['53'])).
% 0.90/1.09  thf('122', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.90/1.09      inference('sat_resolution*', [status(thm)], ['54', '78'])).
% 0.90/1.09  thf('123', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.90/1.09      inference('simpl_trail', [status(thm)], ['121', '122'])).
% 0.90/1.09  thf('124', plain, (((k1_tops_1 @ sk_A @ sk_B) != (sk_B))),
% 0.90/1.09      inference('clc', [status(thm)], ['120', '123'])).
% 0.90/1.09  thf('125', plain, ($false),
% 0.90/1.09      inference('simplify_reflect-', [status(thm)], ['94', '124'])).
% 0.90/1.09  
% 0.90/1.09  % SZS output end Refutation
% 0.90/1.09  
% 0.90/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
