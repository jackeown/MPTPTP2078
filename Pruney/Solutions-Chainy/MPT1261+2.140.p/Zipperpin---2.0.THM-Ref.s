%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TQhyfdz5we

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 195 expanded)
%              Number of leaves         :   41 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          : 1172 (2278 expanded)
%              Number of equality atoms :   93 ( 149 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_tops_1 @ X35 @ X34 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k2_pre_topc @ X35 @ X34 ) @ ( k1_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X37 ) @ X36 @ ( k2_tops_1 @ X37 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('54',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('60',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('70',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X15 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('71',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('72',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','75'])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','76'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('79',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('80',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('81',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['40','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('84',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X32 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('85',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','88'])).

thf('90',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','24','25','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TQhyfdz5we
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:08:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 195 iterations in 0.085s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.20/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(t77_tops_1, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.55             ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.55               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55              ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.55                ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.55                  ( k7_subset_1 @
% 0.20/0.55                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55              (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (~
% 0.20/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55             (k1_tops_1 @ sk_A @ sk_B)))
% 0.20/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t52_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X28 : $i, X29 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.55          | ~ (v4_pre_topc @ X28 @ X29)
% 0.20/0.55          | ((k2_pre_topc @ X29 @ X28) = (X28))
% 0.20/0.55          | ~ (l1_pre_topc @ X29))),
% 0.20/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['3', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(l78_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( k2_tops_1 @ A @ B ) =
% 0.20/0.55             ( k7_subset_1 @
% 0.20/0.55               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.55               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X34 : $i, X35 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.20/0.55          | ((k2_tops_1 @ X35 @ X34)
% 0.20/0.55              = (k7_subset_1 @ (u1_struct_0 @ X35) @ 
% 0.20/0.55                 (k2_pre_topc @ X35 @ X34) @ (k1_tops_1 @ X35 @ X34)))
% 0.20/0.55          | ~ (l1_pre_topc @ X35))),
% 0.20/0.55      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.55            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.20/0.55          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['15', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55              (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.20/0.55             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.55       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k2_tops_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55       ( m1_subset_1 @
% 0.20/0.55         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X30 : $i, X31 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X30)
% 0.20/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.20/0.55          | (m1_subset_1 @ (k2_tops_1 @ X30 @ X31) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.20/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 0.20/0.55          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.55            = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.55         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t65_tops_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.55           ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.55             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X36 : $i, X37 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.20/0.55          | ((k2_pre_topc @ X37 @ X36)
% 0.20/0.55              = (k4_subset_1 @ (u1_struct_0 @ X37) @ X36 @ 
% 0.20/0.55                 (k2_tops_1 @ X37 @ X36)))
% 0.20/0.55          | ~ (l1_pre_topc @ X37))),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.55            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.55         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.55         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['34', '39'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.20/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf(t36_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf(t28_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.55          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.20/0.55          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.55  thf(t100_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.55           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.20/0.55          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.20/0.55             (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['49', '52'])).
% 0.20/0.55  thf(t4_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.55  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 0.20/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.55  thf(d5_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.20/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.55  thf(t3_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('60', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('61', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf('62', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['56', '61'])).
% 0.20/0.55  thf('63', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.20/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.55  thf('65', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.55      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('67', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['67', '68'])).
% 0.20/0.55  thf(dt_k2_subset_1, axiom,
% 0.20/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (![X15 : $i]: (m1_subset_1 @ (k2_subset_1 @ X15) @ (k1_zfmisc_1 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.55  thf('71', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.55  thf('72', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 0.20/0.55      inference('demod', [status(thm)], ['70', '71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.20/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['69', '74'])).
% 0.20/0.55  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['62', '75'])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['53', '76'])).
% 0.20/0.55  thf(t39_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.20/0.55           = (k2_xboole_0 @ X9 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.20/0.55          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['77', '78'])).
% 0.20/0.55  thf(t1_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('80', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['40', '81'])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(fc1_tops_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.55       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      (![X32 : $i, X33 : $i]:
% 0.20/0.55         (~ (l1_pre_topc @ X32)
% 0.20/0.55          | ~ (v2_pre_topc @ X32)
% 0.20/0.55          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.20/0.55          | (v4_pre_topc @ (k2_pre_topc @ X32 @ X33) @ X32))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.55  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('88', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.20/0.55      inference('sup+', [status(thm)], ['82', '88'])).
% 0.20/0.55  thf('90', plain,
% 0.20/0.55      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('91', plain,
% 0.20/0.55      (~
% 0.20/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.20/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.20/0.55       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.55  thf('92', plain, ($false),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['1', '24', '25', '91'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
