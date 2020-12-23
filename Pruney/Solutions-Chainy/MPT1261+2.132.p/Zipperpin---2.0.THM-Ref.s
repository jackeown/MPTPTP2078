%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oQl6TNNpl3

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 171 expanded)
%              Number of leaves         :   33 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          : 1060 (2278 expanded)
%              Number of equality atoms :   81 ( 141 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
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

thf('8',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
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
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_tops_1 @ X42 @ X41 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_pre_topc @ X42 @ X41 ) @ ( k1_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('21',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k4_subset_1 @ X23 @ X22 @ X24 )
        = ( k2_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_pre_topc @ X44 @ X43 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X44 ) @ X43 @ ( k2_tops_1 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('50',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['54','58'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('62',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('63',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('66',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X39 @ X40 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('67',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['64','70'])).

thf('72',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oQl6TNNpl3
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:58:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 308 iterations in 0.126s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.58  thf(t77_tops_1, conjecture,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.58             ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.58               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i]:
% 0.21/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.58          ( ![B:$i]:
% 0.21/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58              ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.58                ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.58                  ( k7_subset_1 @
% 0.21/0.58                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58              (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (~
% 0.21/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.58       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58             (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t52_pre_topc, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.58             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.58               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X35 : $i, X36 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.21/0.58          | ~ (v4_pre_topc @ X35 @ X36)
% 0.21/0.58          | ((k2_pre_topc @ X36 @ X35) = (X35))
% 0.21/0.58          | ~ (l1_pre_topc @ X36))),
% 0.21/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.21/0.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
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
% 0.21/0.58      (![X41 : $i, X42 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.21/0.58          | ((k2_tops_1 @ X42 @ X41)
% 0.21/0.58              = (k7_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.21/0.58                 (k2_pre_topc @ X42 @ X41) @ (k1_tops_1 @ X42 @ X41)))
% 0.21/0.58          | ~ (l1_pre_topc @ X42))),
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
% 0.21/0.58      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58             (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['9', '14'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.21/0.58          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58              (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58         <= (~
% 0.21/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.21/0.58             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.58       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.58       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(dt_k2_tops_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58       ( m1_subset_1 @
% 0.21/0.58         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X37 : $i, X38 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X37)
% 0.21/0.58          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.21/0.58          | (m1_subset_1 @ (k2_tops_1 @ X37 @ X38) @ 
% 0.21/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 0.21/0.58      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.58  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.21/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.21/0.58          | ((k4_subset_1 @ X23 @ X22 @ X24) = (k2_xboole_0 @ X22 @ X24)))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.58            = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.58         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t65_tops_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( l1_pre_topc @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.58           ( ( k2_pre_topc @ A @ B ) =
% 0.21/0.58             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (![X43 : $i, X44 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.21/0.58          | ((k2_pre_topc @ X44 @ X43)
% 0.21/0.58              = (k4_subset_1 @ (u1_struct_0 @ X44) @ X43 @ 
% 0.21/0.58                 (k2_tops_1 @ X44 @ X43)))
% 0.21/0.58          | ~ (l1_pre_topc @ X44))),
% 0.21/0.58      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.58        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.58            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.58         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.58         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['34', '39'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58             (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('split', [status(esa)], ['2'])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.58  thf(t48_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X15 : $i, X16 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.21/0.58           = (k3_xboole_0 @ X15 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.58          = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.58  thf(t47_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.21/0.58           = (k4_xboole_0 @ X13 @ X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      ((((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['45', '46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X15 : $i, X16 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.21/0.58           = (k3_xboole_0 @ X15 @ X16))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.58          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14))
% 0.21/0.58           = (k4_xboole_0 @ X13 @ X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.58           = (k4_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.58          = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['50', '53'])).
% 0.21/0.58  thf(d10_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.58  thf('56', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.58  thf(l32_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.58  thf('57', plain,
% 0.21/0.58      (![X5 : $i, X7 : $i]:
% 0.21/0.58         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.58  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      ((((k1_xboole_0) = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['54', '58'])).
% 0.21/0.58  thf(t39_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.21/0.58           = (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.21/0.58          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.58  thf(t1_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('62', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['40', '63'])).
% 0.21/0.58  thf('65', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(fc1_tops_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.58       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (![X39 : $i, X40 : $i]:
% 0.21/0.58         (~ (l1_pre_topc @ X39)
% 0.21/0.58          | ~ (v2_pre_topc @ X39)
% 0.21/0.58          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.21/0.58          | (v4_pre_topc @ (k2_pre_topc @ X39 @ X40) @ X39))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.21/0.58  thf('67', plain,
% 0.21/0.58      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.58  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('70', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.58      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      (((v4_pre_topc @ sk_B @ sk_A))
% 0.21/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['64', '70'])).
% 0.21/0.58  thf('72', plain,
% 0.21/0.58      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('73', plain,
% 0.21/0.58      (~
% 0.21/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.58       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.58  thf('74', plain, ($false),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '73'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
