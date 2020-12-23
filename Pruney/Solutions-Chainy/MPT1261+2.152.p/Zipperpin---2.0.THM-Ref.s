%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zN4eHIJvrg

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:01 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 265 expanded)
%              Number of leaves         :   39 (  93 expanded)
%              Depth                    :   11
%              Number of atoms          : 1248 (2876 expanded)
%              Number of equality atoms :   89 ( 186 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( v4_pre_topc @ X64 @ X65 )
      | ( ( k2_pre_topc @ X65 @ X64 )
        = X64 )
      | ~ ( l1_pre_topc @ X65 ) ) ),
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
    ! [X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X71 ) ) )
      | ( ( k2_tops_1 @ X71 @ X70 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X71 ) @ ( k2_pre_topc @ X71 @ X70 ) @ ( k1_tops_1 @ X71 @ X70 ) ) )
      | ~ ( l1_pre_topc @ X71 ) ) ),
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
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ( ( k7_subset_1 @ X54 @ X53 @ X55 )
        = ( k4_xboole_0 @ X53 @ X55 ) ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X61: $i,X63: $i] :
      ( ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( r1_tarski @ X61 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('38',plain,(
    ! [X61: $i,X63: $i] :
      ( ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X63 ) )
      | ~ ( r1_tarski @ X61 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('41',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ X57 ) )
      | ( ( k3_subset_1 @ X57 @ ( k7_subset_1 @ X57 @ X58 @ X56 ) )
        = ( k4_subset_1 @ X57 @ ( k3_subset_1 @ X57 @ X58 ) @ X56 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
        | ( ( k3_subset_1 @ sk_B @ ( k7_subset_1 @ sk_B @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
          = ( k4_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k7_subset_1 @ sk_B @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ k1_xboole_0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('45',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ( ( k7_subset_1 @ X54 @ X53 @ X55 )
        = ( k4_xboole_0 @ X53 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','54'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('56',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X45 ) @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('57',plain,(
    ! [X42: $i] :
      ( ( k2_subset_1 @ X42 )
      = X42 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('58',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('59',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k3_subset_1 @ X49 @ ( k3_subset_1 @ X49 @ X48 ) )
        = X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k3_subset_1 @ X43 @ X44 )
        = ( k4_xboole_0 @ X43 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('69',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('70',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) )
      | ( ( k4_subset_1 @ X51 @ X50 @ X52 )
        = ( k2_xboole_0 @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('74',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( l1_pre_topc @ X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X66 @ X67 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('75',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) )
      | ( ( k4_subset_1 @ X51 @ X50 @ X52 )
        = ( k2_xboole_0 @ X50 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('83',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X75 ) ) )
      | ( ( k2_pre_topc @ X75 @ X74 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X75 ) @ X74 @ ( k2_tops_1 @ X75 @ X74 ) ) )
      | ~ ( l1_pre_topc @ X75 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['72','87'])).

thf('89',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','55','66','67','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('91',plain,(
    ! [X68: $i,X69: $i] :
      ( ~ ( l1_pre_topc @ X68 )
      | ~ ( v2_pre_topc @ X68 )
      | ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X68 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X68 @ X69 ) @ X68 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('92',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['89','95'])).

thf('97',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zN4eHIJvrg
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.90/1.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.12  % Solved by: fo/fo7.sh
% 0.90/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.12  % done 1237 iterations in 0.675s
% 0.90/1.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.12  % SZS output start Refutation
% 0.90/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.12  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.90/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.12  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.90/1.12  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.90/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.12  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.90/1.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.12  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.90/1.12  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.90/1.12  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.90/1.12  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.90/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.90/1.12  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.90/1.12  thf(t77_tops_1, conjecture,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12           ( ( v4_pre_topc @ B @ A ) <=>
% 0.90/1.12             ( ( k2_tops_1 @ A @ B ) =
% 0.90/1.12               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.12    (~( ![A:$i]:
% 0.90/1.12        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.90/1.12          ( ![B:$i]:
% 0.90/1.12            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12              ( ( v4_pre_topc @ B @ A ) <=>
% 0.90/1.12                ( ( k2_tops_1 @ A @ B ) =
% 0.90/1.12                  ( k7_subset_1 @
% 0.90/1.12                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.90/1.12    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.90/1.12  thf('0', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12              (k1_tops_1 @ sk_A @ sk_B)))
% 0.90/1.12        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('1', plain,
% 0.90/1.12      (~
% 0.90/1.12       (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.90/1.12       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('2', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12             (k1_tops_1 @ sk_A @ sk_B)))
% 0.90/1.12        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('3', plain,
% 0.90/1.12      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.12      inference('split', [status(esa)], ['2'])).
% 0.90/1.12  thf('4', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(t52_pre_topc, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( l1_pre_topc @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.90/1.12             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.90/1.12               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.90/1.12  thf('5', plain,
% 0.90/1.12      (![X64 : $i, X65 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 0.90/1.12          | ~ (v4_pre_topc @ X64 @ X65)
% 0.90/1.12          | ((k2_pre_topc @ X65 @ X64) = (X64))
% 0.90/1.12          | ~ (l1_pre_topc @ X65))),
% 0.90/1.12      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.90/1.12  thf('6', plain,
% 0.90/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.12        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.90/1.12        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['4', '5'])).
% 0.90/1.12  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('8', plain,
% 0.90/1.12      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.12      inference('demod', [status(thm)], ['6', '7'])).
% 0.90/1.12  thf('9', plain,
% 0.90/1.12      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.90/1.12         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['3', '8'])).
% 0.90/1.12  thf('10', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(l78_tops_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( l1_pre_topc @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12           ( ( k2_tops_1 @ A @ B ) =
% 0.90/1.12             ( k7_subset_1 @
% 0.90/1.12               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.90/1.12               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.12  thf('11', plain,
% 0.90/1.12      (![X70 : $i, X71 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (u1_struct_0 @ X71)))
% 0.90/1.12          | ((k2_tops_1 @ X71 @ X70)
% 0.90/1.12              = (k7_subset_1 @ (u1_struct_0 @ X71) @ 
% 0.90/1.12                 (k2_pre_topc @ X71 @ X70) @ (k1_tops_1 @ X71 @ X70)))
% 0.90/1.12          | ~ (l1_pre_topc @ X71))),
% 0.90/1.12      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.90/1.12  thf('12', plain,
% 0.90/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.12        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.12               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['10', '11'])).
% 0.90/1.12  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('14', plain,
% 0.90/1.12      (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.90/1.12            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['12', '13'])).
% 0.90/1.12  thf('15', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12             (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.12         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.12      inference('sup+', [status(thm)], ['9', '14'])).
% 0.90/1.12  thf('16', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(redefinition_k7_subset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.12       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.90/1.12  thf('17', plain,
% 0.90/1.12      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54))
% 0.90/1.12          | ((k7_subset_1 @ X54 @ X53 @ X55) = (k4_xboole_0 @ X53 @ X55)))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.90/1.12  thf('18', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.90/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.12  thf('19', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.12         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.12      inference('demod', [status(thm)], ['15', '18'])).
% 0.90/1.12  thf('20', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.90/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.12  thf('21', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12              (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.12         <= (~
% 0.90/1.12             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('22', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.12         <= (~
% 0.90/1.12             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['20', '21'])).
% 0.90/1.12  thf('23', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.12         <= (~
% 0.90/1.12             (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.90/1.12             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['19', '22'])).
% 0.90/1.12  thf('24', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.90/1.12       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.12      inference('simplify', [status(thm)], ['23'])).
% 0.90/1.12  thf('25', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.90/1.12       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.12      inference('split', [status(esa)], ['2'])).
% 0.90/1.12  thf(d10_xboole_0, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.12  thf('26', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.90/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.12  thf('27', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.12      inference('simplify', [status(thm)], ['26'])).
% 0.90/1.12  thf(l32_xboole_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.12  thf('28', plain,
% 0.90/1.12      (![X3 : $i, X5 : $i]:
% 0.90/1.12         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.90/1.12      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.12  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.12  thf(t36_xboole_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.12  thf('30', plain,
% 0.90/1.12      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.90/1.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.12  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.12      inference('sup+', [status(thm)], ['29', '30'])).
% 0.90/1.12  thf(t3_subset, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.12  thf('32', plain,
% 0.90/1.12      (![X61 : $i, X63 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X63)) | ~ (r1_tarski @ X61 @ X63))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.12  thf('33', plain,
% 0.90/1.12      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.12  thf('34', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.90/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['16', '17'])).
% 0.90/1.12  thf('35', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12             (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('split', [status(esa)], ['2'])).
% 0.90/1.12  thf('36', plain,
% 0.90/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('sup+', [status(thm)], ['34', '35'])).
% 0.90/1.12  thf('37', plain,
% 0.90/1.12      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.90/1.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.12  thf('38', plain,
% 0.90/1.12      (![X61 : $i, X63 : $i]:
% 0.90/1.12         ((m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X63)) | ~ (r1_tarski @ X61 @ X63))),
% 0.90/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.90/1.12  thf('39', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.12  thf('40', plain,
% 0.90/1.12      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('sup+', [status(thm)], ['36', '39'])).
% 0.90/1.12  thf(t33_subset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.12       ( ![C:$i]:
% 0.90/1.12         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.12           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 0.90/1.12             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.90/1.12  thf('41', plain,
% 0.90/1.12      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ X57))
% 0.90/1.12          | ((k3_subset_1 @ X57 @ (k7_subset_1 @ X57 @ X58 @ X56))
% 0.90/1.12              = (k4_subset_1 @ X57 @ (k3_subset_1 @ X57 @ X58) @ X56))
% 0.90/1.12          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X57)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t33_subset_1])).
% 0.90/1.12  thf('42', plain,
% 0.90/1.12      ((![X0 : $i]:
% 0.90/1.12          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.90/1.12           | ((k3_subset_1 @ sk_B @ 
% 0.90/1.12               (k7_subset_1 @ sk_B @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.12               = (k4_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ X0) @ 
% 0.90/1.12                  (k2_tops_1 @ sk_A @ sk_B)))))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.12  thf('43', plain,
% 0.90/1.12      ((((k3_subset_1 @ sk_B @ 
% 0.90/1.12          (k7_subset_1 @ sk_B @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.90/1.12          = (k4_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ k1_xboole_0) @ 
% 0.90/1.12             (k2_tops_1 @ sk_A @ sk_B))))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['33', '42'])).
% 0.90/1.12  thf('44', plain,
% 0.90/1.12      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.12  thf('45', plain,
% 0.90/1.12      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54))
% 0.90/1.12          | ((k7_subset_1 @ X54 @ X53 @ X55) = (k4_xboole_0 @ X53 @ X55)))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.90/1.12  thf('46', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 0.90/1.12           = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 0.90/1.12      inference('sup-', [status(thm)], ['44', '45'])).
% 0.90/1.12  thf(t100_xboole_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.90/1.12  thf('47', plain,
% 0.90/1.12      (![X6 : $i, X7 : $i]:
% 0.90/1.12         ((k4_xboole_0 @ X6 @ X7)
% 0.90/1.12           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.12  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.12  thf('49', plain,
% 0.90/1.12      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.90/1.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.90/1.12  thf('50', plain,
% 0.90/1.12      (![X3 : $i, X5 : $i]:
% 0.90/1.12         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.90/1.12      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.90/1.12  thf('51', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.12  thf('52', plain,
% 0.90/1.12      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.12      inference('sup+', [status(thm)], ['48', '51'])).
% 0.90/1.12  thf('53', plain,
% 0.90/1.12      (![X6 : $i, X7 : $i]:
% 0.90/1.12         ((k4_xboole_0 @ X6 @ X7)
% 0.90/1.12           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.90/1.12  thf('54', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.90/1.12           = (k1_xboole_0))),
% 0.90/1.12      inference('demod', [status(thm)], ['52', '53'])).
% 0.90/1.12  thf('55', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.90/1.12      inference('demod', [status(thm)], ['46', '47', '54'])).
% 0.90/1.12  thf(dt_k2_subset_1, axiom,
% 0.90/1.12    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.12  thf('56', plain,
% 0.90/1.12      (![X45 : $i]: (m1_subset_1 @ (k2_subset_1 @ X45) @ (k1_zfmisc_1 @ X45))),
% 0.90/1.12      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.90/1.12  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.90/1.12  thf('57', plain, (![X42 : $i]: ((k2_subset_1 @ X42) = (X42))),
% 0.90/1.12      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.90/1.12  thf('58', plain, (![X45 : $i]: (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X45))),
% 0.90/1.12      inference('demod', [status(thm)], ['56', '57'])).
% 0.90/1.12  thf(involutiveness_k3_subset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.12       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.90/1.12  thf('59', plain,
% 0.90/1.12      (![X48 : $i, X49 : $i]:
% 0.90/1.12         (((k3_subset_1 @ X49 @ (k3_subset_1 @ X49 @ X48)) = (X48))
% 0.90/1.12          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 0.90/1.12      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.90/1.12  thf('60', plain,
% 0.90/1.12      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['58', '59'])).
% 0.90/1.12  thf('61', plain, (![X45 : $i]: (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X45))),
% 0.90/1.12      inference('demod', [status(thm)], ['56', '57'])).
% 0.90/1.12  thf(d5_subset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.12       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.90/1.12  thf('62', plain,
% 0.90/1.12      (![X43 : $i, X44 : $i]:
% 0.90/1.12         (((k3_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))
% 0.90/1.12          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43)))),
% 0.90/1.12      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.90/1.12  thf('63', plain,
% 0.90/1.12      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['61', '62'])).
% 0.90/1.12  thf('64', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.12      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.12  thf('65', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.12      inference('demod', [status(thm)], ['63', '64'])).
% 0.90/1.12  thf('66', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.12      inference('demod', [status(thm)], ['60', '65'])).
% 0.90/1.12  thf('67', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.90/1.12      inference('demod', [status(thm)], ['60', '65'])).
% 0.90/1.12  thf('68', plain,
% 0.90/1.12      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('sup+', [status(thm)], ['36', '39'])).
% 0.90/1.12  thf('69', plain, (![X45 : $i]: (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X45))),
% 0.90/1.12      inference('demod', [status(thm)], ['56', '57'])).
% 0.90/1.12  thf(redefinition_k4_subset_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.90/1.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.12       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.90/1.12  thf('70', plain,
% 0.90/1.12      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.90/1.12          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51))
% 0.90/1.12          | ((k4_subset_1 @ X51 @ X50 @ X52) = (k2_xboole_0 @ X50 @ X52)))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.90/1.12  thf('71', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 0.90/1.12          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['69', '70'])).
% 0.90/1.12  thf('72', plain,
% 0.90/1.12      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.12          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['68', '71'])).
% 0.90/1.12  thf('73', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(dt_k2_tops_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( l1_pre_topc @ A ) & 
% 0.90/1.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.12       ( m1_subset_1 @
% 0.90/1.12         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.12  thf('74', plain,
% 0.90/1.12      (![X66 : $i, X67 : $i]:
% 0.90/1.12         (~ (l1_pre_topc @ X66)
% 0.90/1.12          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 0.90/1.12          | (m1_subset_1 @ (k2_tops_1 @ X66 @ X67) @ 
% 0.90/1.12             (k1_zfmisc_1 @ (u1_struct_0 @ X66))))),
% 0.90/1.12      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.90/1.12  thf('75', plain,
% 0.90/1.12      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.12        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['73', '74'])).
% 0.90/1.12  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('77', plain,
% 0.90/1.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.12      inference('demod', [status(thm)], ['75', '76'])).
% 0.90/1.12  thf('78', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('79', plain,
% 0.90/1.12      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 0.90/1.12          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51))
% 0.90/1.12          | ((k4_subset_1 @ X51 @ X50 @ X52) = (k2_xboole_0 @ X50 @ X52)))),
% 0.90/1.12      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.90/1.12  thf('80', plain,
% 0.90/1.12      (![X0 : $i]:
% 0.90/1.12         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.90/1.12            = (k2_xboole_0 @ sk_B @ X0))
% 0.90/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['78', '79'])).
% 0.90/1.12  thf('81', plain,
% 0.90/1.12      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.12         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['77', '80'])).
% 0.90/1.12  thf('82', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(t65_tops_1, axiom,
% 0.90/1.12    (![A:$i]:
% 0.90/1.12     ( ( l1_pre_topc @ A ) =>
% 0.90/1.12       ( ![B:$i]:
% 0.90/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.12           ( ( k2_pre_topc @ A @ B ) =
% 0.90/1.12             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.12  thf('83', plain,
% 0.90/1.12      (![X74 : $i, X75 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (u1_struct_0 @ X75)))
% 0.90/1.12          | ((k2_pre_topc @ X75 @ X74)
% 0.90/1.12              = (k4_subset_1 @ (u1_struct_0 @ X75) @ X74 @ 
% 0.90/1.12                 (k2_tops_1 @ X75 @ X74)))
% 0.90/1.12          | ~ (l1_pre_topc @ X75))),
% 0.90/1.12      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.90/1.12  thf('84', plain,
% 0.90/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.12        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.90/1.12            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.90/1.12      inference('sup-', [status(thm)], ['82', '83'])).
% 0.90/1.12  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('86', plain,
% 0.90/1.12      (((k2_pre_topc @ sk_A @ sk_B)
% 0.90/1.12         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('demod', [status(thm)], ['84', '85'])).
% 0.90/1.12  thf('87', plain,
% 0.90/1.12      (((k2_pre_topc @ sk_A @ sk_B)
% 0.90/1.12         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup+', [status(thm)], ['81', '86'])).
% 0.90/1.12  thf('88', plain,
% 0.90/1.12      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.12          = (k2_pre_topc @ sk_A @ sk_B)))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('demod', [status(thm)], ['72', '87'])).
% 0.90/1.12  thf('89', plain,
% 0.90/1.12      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('demod', [status(thm)], ['43', '55', '66', '67', '88'])).
% 0.90/1.12  thf('90', plain,
% 0.90/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(fc1_tops_1, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.90/1.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.12       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.90/1.12  thf('91', plain,
% 0.90/1.12      (![X68 : $i, X69 : $i]:
% 0.90/1.12         (~ (l1_pre_topc @ X68)
% 0.90/1.12          | ~ (v2_pre_topc @ X68)
% 0.90/1.12          | ~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X68)))
% 0.90/1.12          | (v4_pre_topc @ (k2_pre_topc @ X68 @ X69) @ X68))),
% 0.90/1.12      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.90/1.12  thf('92', plain,
% 0.90/1.12      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.90/1.12        | ~ (v2_pre_topc @ sk_A)
% 0.90/1.12        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['90', '91'])).
% 0.90/1.12  thf('93', plain, ((v2_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('95', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.90/1.12      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.90/1.12  thf('96', plain,
% 0.90/1.12      (((v4_pre_topc @ sk_B @ sk_A))
% 0.90/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.12      inference('sup+', [status(thm)], ['89', '95'])).
% 0.90/1.12  thf('97', plain,
% 0.90/1.12      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.90/1.12      inference('split', [status(esa)], ['0'])).
% 0.90/1.12  thf('98', plain,
% 0.90/1.12      (~
% 0.90/1.12       (((k2_tops_1 @ sk_A @ sk_B)
% 0.90/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.90/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.90/1.12       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['96', '97'])).
% 0.90/1.12  thf('99', plain, ($false),
% 0.90/1.12      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '98'])).
% 0.90/1.12  
% 0.90/1.12  % SZS output end Refutation
% 0.90/1.12  
% 0.90/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
