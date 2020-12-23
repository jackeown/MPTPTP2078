%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fm1k37FhPQ

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:01 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 205 expanded)
%              Number of leaves         :   38 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          : 1137 (2308 expanded)
%              Number of equality atoms :   83 ( 140 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v4_pre_topc @ X33 @ X34 )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = X33 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k2_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k4_subset_1 @ X25 @ X24 @ X26 )
        = ( k2_xboole_0 @ X24 @ X26 ) ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_pre_topc @ X42 @ X41 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 @ ( k2_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('64',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','79'])).

thf('81',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('82',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','80','81'])).

thf('83',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('85',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X37 @ X38 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('86',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['83','89'])).

thf('91',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fm1k37FhPQ
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.74/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.93  % Solved by: fo/fo7.sh
% 0.74/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.93  % done 1732 iterations in 0.469s
% 0.74/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.93  % SZS output start Refutation
% 0.74/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.93  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.74/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.74/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.93  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.74/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.93  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.74/0.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.74/0.93  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.74/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.93  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.74/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.93  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.74/0.93  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.74/0.93  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.74/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(t77_tops_1, conjecture,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( v4_pre_topc @ B @ A ) <=>
% 0.74/0.93             ( ( k2_tops_1 @ A @ B ) =
% 0.74/0.93               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.93    (~( ![A:$i]:
% 0.74/0.93        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.74/0.93          ( ![B:$i]:
% 0.74/0.93            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93              ( ( v4_pre_topc @ B @ A ) <=>
% 0.74/0.93                ( ( k2_tops_1 @ A @ B ) =
% 0.74/0.93                  ( k7_subset_1 @
% 0.74/0.93                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.74/0.93    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.74/0.93  thf('0', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93              (k1_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('1', plain,
% 0.74/0.93      (~
% 0.74/0.93       (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.74/0.93       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('2', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('3', plain,
% 0.74/0.93      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('split', [status(esa)], ['2'])).
% 0.74/0.93  thf('4', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t52_pre_topc, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.74/0.93             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.74/0.93               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.74/0.93  thf('5', plain,
% 0.74/0.93      (![X33 : $i, X34 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.74/0.93          | ~ (v4_pre_topc @ X33 @ X34)
% 0.74/0.93          | ((k2_pre_topc @ X34 @ X33) = (X33))
% 0.74/0.93          | ~ (l1_pre_topc @ X34))),
% 0.74/0.93      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.74/0.93  thf('6', plain,
% 0.74/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.74/0.93        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.74/0.93        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.74/0.93  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('8', plain,
% 0.74/0.93      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('demod', [status(thm)], ['6', '7'])).
% 0.74/0.93  thf('9', plain,
% 0.74/0.93      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['3', '8'])).
% 0.74/0.93  thf('10', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(l78_tops_1, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( k2_tops_1 @ A @ B ) =
% 0.74/0.93             ( k7_subset_1 @
% 0.74/0.93               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.74/0.93               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.74/0.93  thf('11', plain,
% 0.74/0.93      (![X39 : $i, X40 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.74/0.93          | ((k2_tops_1 @ X40 @ X39)
% 0.74/0.93              = (k7_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.74/0.93                 (k2_pre_topc @ X40 @ X39) @ (k1_tops_1 @ X40 @ X39)))
% 0.74/0.93          | ~ (l1_pre_topc @ X40))),
% 0.74/0.93      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.74/0.93  thf('12', plain,
% 0.74/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.74/0.93        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.74/0.93               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/0.93  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('14', plain,
% 0.74/0.93      (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.74/0.93            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('demod', [status(thm)], ['12', '13'])).
% 0.74/0.93  thf('15', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['9', '14'])).
% 0.74/0.93  thf('16', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k7_subset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.93       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.74/0.93  thf('17', plain,
% 0.74/0.93      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.74/0.93          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.74/0.93  thf('18', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93           = (k4_xboole_0 @ sk_B @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['16', '17'])).
% 0.74/0.93  thf('19', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('demod', [status(thm)], ['15', '18'])).
% 0.74/0.93  thf('20', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93           = (k4_xboole_0 @ sk_B @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['16', '17'])).
% 0.74/0.93  thf('21', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93              (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (~
% 0.74/0.93             (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('22', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= (~
% 0.74/0.93             (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['20', '21'])).
% 0.74/0.93  thf('23', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93         <= (~
% 0.74/0.93             (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.74/0.93             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['19', '22'])).
% 0.74/0.93  thf('24', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.74/0.93       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('simplify', [status(thm)], ['23'])).
% 0.74/0.93  thf('25', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.74/0.93       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('split', [status(esa)], ['2'])).
% 0.74/0.93  thf('26', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(dt_k2_tops_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( l1_pre_topc @ A ) & 
% 0.74/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.93       ( m1_subset_1 @
% 0.74/0.93         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.74/0.93  thf('27', plain,
% 0.74/0.93      (![X35 : $i, X36 : $i]:
% 0.74/0.93         (~ (l1_pre_topc @ X35)
% 0.74/0.93          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.74/0.93          | (m1_subset_1 @ (k2_tops_1 @ X35 @ X36) @ 
% 0.74/0.93             (k1_zfmisc_1 @ (u1_struct_0 @ X35))))),
% 0.74/0.93      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.74/0.93  thf('28', plain,
% 0.74/0.93      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.74/0.93         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.74/0.93        | ~ (l1_pre_topc @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.74/0.93  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('30', plain,
% 0.74/0.93      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.74/0.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('demod', [status(thm)], ['28', '29'])).
% 0.74/0.93  thf('31', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k4_subset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.74/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.74/0.93       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.74/0.93  thf('32', plain,
% 0.74/0.93      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.74/0.93          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25))
% 0.74/0.93          | ((k4_subset_1 @ X25 @ X24 @ X26) = (k2_xboole_0 @ X24 @ X26)))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.74/0.93  thf('33', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93            = (k2_xboole_0 @ sk_B @ X0))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['31', '32'])).
% 0.74/0.93  thf('34', plain,
% 0.74/0.93      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.74/0.93         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['30', '33'])).
% 0.74/0.93  thf('35', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t65_tops_1, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( k2_pre_topc @ A @ B ) =
% 0.74/0.93             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.74/0.93  thf('36', plain,
% 0.74/0.93      (![X41 : $i, X42 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.74/0.93          | ((k2_pre_topc @ X42 @ X41)
% 0.74/0.93              = (k4_subset_1 @ (u1_struct_0 @ X42) @ X41 @ 
% 0.74/0.93                 (k2_tops_1 @ X42 @ X41)))
% 0.74/0.93          | ~ (l1_pre_topc @ X42))),
% 0.74/0.93      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.74/0.93  thf('37', plain,
% 0.74/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.74/0.93        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.74/0.93            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['35', '36'])).
% 0.74/0.93  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('39', plain,
% 0.74/0.93      (((k2_pre_topc @ sk_A @ sk_B)
% 0.74/0.93         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('demod', [status(thm)], ['37', '38'])).
% 0.74/0.93  thf('40', plain,
% 0.74/0.93      (((k2_pre_topc @ sk_A @ sk_B)
% 0.74/0.93         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('sup+', [status(thm)], ['34', '39'])).
% 0.74/0.93  thf('41', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.74/0.93           = (k4_xboole_0 @ sk_B @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['16', '17'])).
% 0.74/0.93  thf('42', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('split', [status(esa)], ['2'])).
% 0.74/0.93  thf('43', plain,
% 0.74/0.93      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['41', '42'])).
% 0.74/0.93  thf(t36_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.74/0.93  thf('44', plain,
% 0.74/0.93      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.74/0.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/0.93  thf('45', plain,
% 0.74/0.93      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['43', '44'])).
% 0.74/0.93  thf(t28_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.74/0.93  thf('46', plain,
% 0.74/0.93      (![X6 : $i, X7 : $i]:
% 0.74/0.93         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.74/0.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.74/0.93  thf('47', plain,
% 0.74/0.93      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.74/0.93          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.74/0.93  thf(t100_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.74/0.93  thf('48', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X3 @ X4)
% 0.74/0.93           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.93  thf(t39_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.93  thf('49', plain,
% 0.74/0.93      (![X10 : $i, X11 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.74/0.93           = (k2_xboole_0 @ X10 @ X11))),
% 0.74/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.74/0.93  thf('50', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.74/0.93           = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('sup+', [status(thm)], ['48', '49'])).
% 0.74/0.93  thf('51', plain,
% 0.74/0.93      ((((k2_xboole_0 @ sk_B @ 
% 0.74/0.93          (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.74/0.93          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['47', '50'])).
% 0.74/0.93  thf(t1_boole, axiom,
% 0.74/0.93    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.74/0.93  thf('52', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.74/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.74/0.93  thf('53', plain,
% 0.74/0.93      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.74/0.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/0.93  thf(t44_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.74/0.93       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.74/0.93  thf('54', plain,
% 0.74/0.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.74/0.93         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.74/0.93          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 0.74/0.93      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.74/0.93  thf('55', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['53', '54'])).
% 0.74/0.93  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.74/0.93      inference('sup+', [status(thm)], ['52', '55'])).
% 0.74/0.93  thf(t3_subset, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.74/0.93  thf('57', plain,
% 0.74/0.93      (![X30 : $i, X32 : $i]:
% 0.74/0.93         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.74/0.93  thf('58', plain,
% 0.74/0.93      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['56', '57'])).
% 0.74/0.93  thf(involutiveness_k3_subset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.93       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.74/0.93  thf('59', plain,
% 0.74/0.93      (![X22 : $i, X23 : $i]:
% 0.74/0.93         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.74/0.93          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.74/0.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.74/0.93  thf('60', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['58', '59'])).
% 0.74/0.93  thf('61', plain,
% 0.74/0.93      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['56', '57'])).
% 0.74/0.93  thf(d5_subset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.93       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.74/0.93  thf('62', plain,
% 0.74/0.93      (![X19 : $i, X20 : $i]:
% 0.74/0.93         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.74/0.93          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.74/0.93  thf('63', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['61', '62'])).
% 0.74/0.93  thf(t3_boole, axiom,
% 0.74/0.93    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.74/0.93  thf('64', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf('65', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['63', '64'])).
% 0.74/0.93  thf('66', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/0.93      inference('demod', [status(thm)], ['60', '65'])).
% 0.74/0.93  thf('67', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_boole])).
% 0.74/0.93  thf('68', plain,
% 0.74/0.93      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.74/0.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.74/0.93  thf('69', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.74/0.93      inference('sup+', [status(thm)], ['67', '68'])).
% 0.74/0.93  thf('70', plain,
% 0.74/0.93      (![X30 : $i, X32 : $i]:
% 0.74/0.93         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.74/0.93  thf('71', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['69', '70'])).
% 0.74/0.93  thf('72', plain,
% 0.74/0.93      (![X19 : $i, X20 : $i]:
% 0.74/0.93         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.74/0.93          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.74/0.93  thf('73', plain,
% 0.74/0.93      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['71', '72'])).
% 0.74/0.93  thf('74', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.74/0.93      inference('sup+', [status(thm)], ['67', '68'])).
% 0.74/0.93  thf('75', plain,
% 0.74/0.93      (![X6 : $i, X7 : $i]:
% 0.74/0.93         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.74/0.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.74/0.93  thf('76', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['74', '75'])).
% 0.74/0.93  thf('77', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i]:
% 0.74/0.93         ((k4_xboole_0 @ X3 @ X4)
% 0.74/0.93           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.74/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.74/0.93  thf('78', plain,
% 0.74/0.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['76', '77'])).
% 0.74/0.93  thf('79', plain,
% 0.74/0.93      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['73', '78'])).
% 0.74/0.93  thf('80', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.74/0.93      inference('demod', [status(thm)], ['66', '79'])).
% 0.74/0.93  thf('81', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.74/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.74/0.93  thf('82', plain,
% 0.74/0.93      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('demod', [status(thm)], ['51', '80', '81'])).
% 0.74/0.93  thf('83', plain,
% 0.74/0.93      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['40', '82'])).
% 0.74/0.93  thf('84', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(fc1_tops_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.74/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.93       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.74/0.93  thf('85', plain,
% 0.74/0.93      (![X37 : $i, X38 : $i]:
% 0.74/0.93         (~ (l1_pre_topc @ X37)
% 0.74/0.93          | ~ (v2_pre_topc @ X37)
% 0.74/0.93          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.74/0.93          | (v4_pre_topc @ (k2_pre_topc @ X37 @ X38) @ X37))),
% 0.74/0.93      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.74/0.93  thf('86', plain,
% 0.74/0.93      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.74/0.93        | ~ (v2_pre_topc @ sk_A)
% 0.74/0.93        | ~ (l1_pre_topc @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['84', '85'])).
% 0.74/0.93  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('89', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.74/0.93      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.74/0.93  thf('90', plain,
% 0.74/0.93      (((v4_pre_topc @ sk_B @ sk_A))
% 0.74/0.93         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.74/0.93      inference('sup+', [status(thm)], ['83', '89'])).
% 0.74/0.93  thf('91', plain,
% 0.74/0.93      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('92', plain,
% 0.74/0.93      (~
% 0.74/0.93       (((k2_tops_1 @ sk_A @ sk_B)
% 0.74/0.93          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.74/0.93             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.74/0.93       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['90', '91'])).
% 0.74/0.93  thf('93', plain, ($false),
% 0.74/0.93      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '92'])).
% 0.74/0.93  
% 0.74/0.93  % SZS output end Refutation
% 0.74/0.93  
% 0.74/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
