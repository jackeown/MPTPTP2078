%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LQlPaGnH8V

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:44 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 209 expanded)
%              Number of leaves         :   40 (  76 expanded)
%              Depth                    :   16
%              Number of atoms          : 1186 (2424 expanded)
%              Number of equality atoms :   97 ( 171 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k1_tops_1 @ X50 @ X49 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 @ ( k2_tops_1 @ X50 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('15',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X48 @ X47 ) @ X47 )
      | ~ ( v4_pre_topc @ X47 @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('45',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('54',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('56',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('58',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','61'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('63',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('66',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('70',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68','73'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['62','74'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('76',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('77',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('78',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('79',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['49','79'])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v2_pre_topc @ X40 )
      | ( ( k2_pre_topc @ X40 @ X39 )
       != X39 )
      | ( v4_pre_topc @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('83',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','34','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LQlPaGnH8V
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:34:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.12  % Solved by: fo/fo7.sh
% 0.89/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.12  % done 1791 iterations in 0.662s
% 0.89/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.12  % SZS output start Refutation
% 0.89/1.12  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.89/1.12  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.89/1.12  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.89/1.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.12  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.89/1.12  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.12  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.12  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.89/1.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.89/1.12  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.89/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.89/1.12  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.89/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.89/1.12  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.89/1.12  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.12  thf(t77_tops_1, conjecture,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.12       ( ![B:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.12           ( ( v4_pre_topc @ B @ A ) <=>
% 0.89/1.12             ( ( k2_tops_1 @ A @ B ) =
% 0.89/1.12               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.89/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.12    (~( ![A:$i]:
% 0.89/1.12        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.12          ( ![B:$i]:
% 0.89/1.12            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.12              ( ( v4_pre_topc @ B @ A ) <=>
% 0.89/1.12                ( ( k2_tops_1 @ A @ B ) =
% 0.89/1.12                  ( k7_subset_1 @
% 0.89/1.12                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.89/1.12    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.89/1.12  thf('0', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12              (k1_tops_1 @ sk_A @ sk_B)))
% 0.89/1.12        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('1', plain,
% 0.89/1.12      (~
% 0.89/1.12       (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.89/1.12       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.12      inference('split', [status(esa)], ['0'])).
% 0.89/1.12  thf('2', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(t74_tops_1, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( l1_pre_topc @ A ) =>
% 0.89/1.12       ( ![B:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.12           ( ( k1_tops_1 @ A @ B ) =
% 0.89/1.12             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.12  thf('3', plain,
% 0.89/1.12      (![X49 : $i, X50 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 0.89/1.12          | ((k1_tops_1 @ X50 @ X49)
% 0.89/1.12              = (k7_subset_1 @ (u1_struct_0 @ X50) @ X49 @ 
% 0.89/1.12                 (k2_tops_1 @ X50 @ X49)))
% 0.89/1.12          | ~ (l1_pre_topc @ X50))),
% 0.89/1.12      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.89/1.12  thf('4', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.12        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.12            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['2', '3'])).
% 0.89/1.12  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('6', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(redefinition_k7_subset_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.12       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.89/1.12  thf('7', plain,
% 0.89/1.12      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.89/1.12          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 0.89/1.12      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.89/1.12  thf('8', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.12  thf('9', plain,
% 0.89/1.12      (((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.12         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.12      inference('demod', [status(thm)], ['4', '5', '8'])).
% 0.89/1.12  thf(t48_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.89/1.12  thf('10', plain,
% 0.89/1.12      (![X18 : $i, X19 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.89/1.12           = (k3_xboole_0 @ X18 @ X19))),
% 0.89/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.12  thf('11', plain,
% 0.89/1.12      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.89/1.12         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['9', '10'])).
% 0.89/1.12  thf('12', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12             (k1_tops_1 @ sk_A @ sk_B)))
% 0.89/1.12        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('13', plain,
% 0.89/1.12      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.12      inference('split', [status(esa)], ['12'])).
% 0.89/1.12  thf('14', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(t69_tops_1, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( l1_pre_topc @ A ) =>
% 0.89/1.12       ( ![B:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.12           ( ( v4_pre_topc @ B @ A ) =>
% 0.89/1.12             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.89/1.12  thf('15', plain,
% 0.89/1.12      (![X47 : $i, X48 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.89/1.12          | (r1_tarski @ (k2_tops_1 @ X48 @ X47) @ X47)
% 0.89/1.12          | ~ (v4_pre_topc @ X47 @ X48)
% 0.89/1.12          | ~ (l1_pre_topc @ X48))),
% 0.89/1.12      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.89/1.12  thf('16', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.12        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.89/1.12        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.89/1.12      inference('sup-', [status(thm)], ['14', '15'])).
% 0.89/1.12  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('18', plain,
% 0.89/1.12      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.89/1.12        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.89/1.12      inference('demod', [status(thm)], ['16', '17'])).
% 0.89/1.12  thf('19', plain,
% 0.89/1.12      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.89/1.12         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['13', '18'])).
% 0.89/1.12  thf(t28_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.89/1.12  thf('20', plain,
% 0.89/1.12      (![X10 : $i, X11 : $i]:
% 0.89/1.12         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.89/1.12      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.89/1.12  thf('21', plain,
% 0.89/1.12      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.89/1.12          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.12         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.12  thf(commutativity_k2_tarski, axiom,
% 0.89/1.12    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.89/1.12  thf('22', plain,
% 0.89/1.12      (![X20 : $i, X21 : $i]:
% 0.89/1.12         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 0.89/1.12      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.89/1.12  thf(t12_setfam_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.89/1.12  thf('23', plain,
% 0.89/1.12      (![X34 : $i, X35 : $i]:
% 0.89/1.12         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 0.89/1.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.89/1.12  thf('24', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.12      inference('sup+', [status(thm)], ['22', '23'])).
% 0.89/1.12  thf('25', plain,
% 0.89/1.12      (![X34 : $i, X35 : $i]:
% 0.89/1.12         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 0.89/1.12      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.89/1.12  thf('26', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.12      inference('sup+', [status(thm)], ['24', '25'])).
% 0.89/1.12  thf('27', plain,
% 0.89/1.12      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.89/1.12          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.12         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.12      inference('demod', [status(thm)], ['21', '26'])).
% 0.89/1.12  thf('28', plain,
% 0.89/1.12      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.89/1.12          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.12         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['11', '27'])).
% 0.89/1.12  thf('29', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.12  thf('30', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12              (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('split', [status(esa)], ['0'])).
% 0.89/1.12  thf('31', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['29', '30'])).
% 0.89/1.12  thf('32', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.12         <= (~
% 0.89/1.12             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.89/1.12             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['28', '31'])).
% 0.89/1.12  thf('33', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.89/1.12       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.12      inference('simplify', [status(thm)], ['32'])).
% 0.89/1.12  thf('34', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.89/1.12       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.12      inference('split', [status(esa)], ['12'])).
% 0.89/1.12  thf('35', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(dt_k2_tops_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( ( l1_pre_topc @ A ) & 
% 0.89/1.12         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.89/1.12       ( m1_subset_1 @
% 0.89/1.12         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.89/1.12  thf('36', plain,
% 0.89/1.12      (![X41 : $i, X42 : $i]:
% 0.89/1.12         (~ (l1_pre_topc @ X41)
% 0.89/1.12          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.89/1.12          | (m1_subset_1 @ (k2_tops_1 @ X41 @ X42) @ 
% 0.89/1.12             (k1_zfmisc_1 @ (u1_struct_0 @ X41))))),
% 0.89/1.12      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.89/1.12  thf('37', plain,
% 0.89/1.12      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.89/1.12         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.12        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.89/1.12  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('39', plain,
% 0.89/1.12      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.89/1.12        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('demod', [status(thm)], ['37', '38'])).
% 0.89/1.12  thf('40', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(redefinition_k4_subset_1, axiom,
% 0.89/1.12    (![A:$i,B:$i,C:$i]:
% 0.89/1.12     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.89/1.12         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.89/1.12       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.89/1.12  thf('41', plain,
% 0.89/1.12      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 0.89/1.12          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 0.89/1.12          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 0.89/1.12      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.89/1.12  thf('42', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.12            = (k2_xboole_0 @ sk_B @ X0))
% 0.89/1.12          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.89/1.12  thf('43', plain,
% 0.89/1.12      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.89/1.12         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.12      inference('sup-', [status(thm)], ['39', '42'])).
% 0.89/1.12  thf('44', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(t65_tops_1, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( l1_pre_topc @ A ) =>
% 0.89/1.12       ( ![B:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.12           ( ( k2_pre_topc @ A @ B ) =
% 0.89/1.12             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.12  thf('45', plain,
% 0.89/1.12      (![X45 : $i, X46 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.89/1.12          | ((k2_pre_topc @ X46 @ X45)
% 0.89/1.12              = (k4_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 0.89/1.12                 (k2_tops_1 @ X46 @ X45)))
% 0.89/1.12          | ~ (l1_pre_topc @ X46))),
% 0.89/1.12      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.89/1.12  thf('46', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.12        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.89/1.12            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['44', '45'])).
% 0.89/1.12  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('48', plain,
% 0.89/1.12      (((k2_pre_topc @ sk_A @ sk_B)
% 0.89/1.12         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.12      inference('demod', [status(thm)], ['46', '47'])).
% 0.89/1.12  thf('49', plain,
% 0.89/1.12      (((k2_pre_topc @ sk_A @ sk_B)
% 0.89/1.12         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['43', '48'])).
% 0.89/1.12  thf('50', plain,
% 0.89/1.12      (![X0 : $i]:
% 0.89/1.12         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.12           = (k4_xboole_0 @ sk_B @ X0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.12  thf('51', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12             (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('split', [status(esa)], ['12'])).
% 0.89/1.12  thf('52', plain,
% 0.89/1.12      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('sup+', [status(thm)], ['50', '51'])).
% 0.89/1.12  thf(t36_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.89/1.12  thf('53', plain,
% 0.89/1.12      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.89/1.12      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.89/1.12  thf('54', plain,
% 0.89/1.12      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('sup+', [status(thm)], ['52', '53'])).
% 0.89/1.12  thf('55', plain,
% 0.89/1.12      (![X10 : $i, X11 : $i]:
% 0.89/1.12         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.89/1.12      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.89/1.12  thf('56', plain,
% 0.89/1.12      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.89/1.12          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['54', '55'])).
% 0.89/1.12  thf('57', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.12      inference('sup+', [status(thm)], ['24', '25'])).
% 0.89/1.12  thf('58', plain,
% 0.89/1.12      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.89/1.12          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('demod', [status(thm)], ['56', '57'])).
% 0.89/1.12  thf('59', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.12      inference('sup+', [status(thm)], ['24', '25'])).
% 0.89/1.12  thf(t100_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.89/1.12  thf('60', plain,
% 0.89/1.12      (![X7 : $i, X8 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X7 @ X8)
% 0.89/1.12           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.89/1.12  thf('61', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X0 @ X1)
% 0.89/1.12           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.89/1.12      inference('sup+', [status(thm)], ['59', '60'])).
% 0.89/1.12  thf('62', plain,
% 0.89/1.12      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.89/1.12          = (k5_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.89/1.12             (k2_tops_1 @ sk_A @ sk_B))))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('sup+', [status(thm)], ['58', '61'])).
% 0.89/1.12  thf(t3_boole, axiom,
% 0.89/1.12    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.12  thf('63', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.89/1.12      inference('cnf', [status(esa)], [t3_boole])).
% 0.89/1.12  thf('64', plain,
% 0.89/1.12      (![X18 : $i, X19 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.89/1.12           = (k3_xboole_0 @ X18 @ X19))),
% 0.89/1.12      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.89/1.12  thf('65', plain,
% 0.89/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['63', '64'])).
% 0.89/1.12  thf(idempotence_k3_xboole_0, axiom,
% 0.89/1.12    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.89/1.12  thf('66', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.89/1.12      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.89/1.12  thf('67', plain,
% 0.89/1.12      (![X7 : $i, X8 : $i]:
% 0.89/1.12         ((k4_xboole_0 @ X7 @ X8)
% 0.89/1.12           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.89/1.12      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.89/1.12  thf('68', plain,
% 0.89/1.12      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['66', '67'])).
% 0.89/1.12  thf('69', plain,
% 0.89/1.12      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.89/1.12      inference('sup+', [status(thm)], ['24', '25'])).
% 0.89/1.12  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.89/1.12  thf('70', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.89/1.12      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.89/1.12  thf('71', plain,
% 0.89/1.12      (![X10 : $i, X11 : $i]:
% 0.89/1.12         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.89/1.12      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.89/1.12  thf('72', plain,
% 0.89/1.12      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.89/1.12      inference('sup-', [status(thm)], ['70', '71'])).
% 0.89/1.12  thf('73', plain,
% 0.89/1.12      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.12      inference('sup+', [status(thm)], ['69', '72'])).
% 0.89/1.12  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.89/1.12      inference('demod', [status(thm)], ['65', '68', '73'])).
% 0.89/1.12  thf('75', plain,
% 0.89/1.12      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('demod', [status(thm)], ['62', '74'])).
% 0.89/1.12  thf(t39_xboole_1, axiom,
% 0.89/1.12    (![A:$i,B:$i]:
% 0.89/1.12     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.89/1.12  thf('76', plain,
% 0.89/1.12      (![X15 : $i, X16 : $i]:
% 0.89/1.12         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.89/1.12           = (k2_xboole_0 @ X15 @ X16))),
% 0.89/1.12      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.12  thf('77', plain,
% 0.89/1.12      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.89/1.12          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('sup+', [status(thm)], ['75', '76'])).
% 0.89/1.12  thf(t1_boole, axiom,
% 0.89/1.12    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.12  thf('78', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.89/1.12      inference('cnf', [status(esa)], [t1_boole])).
% 0.89/1.12  thf('79', plain,
% 0.89/1.12      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('demod', [status(thm)], ['77', '78'])).
% 0.89/1.12  thf('80', plain,
% 0.89/1.12      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('sup+', [status(thm)], ['49', '79'])).
% 0.89/1.12  thf('81', plain,
% 0.89/1.12      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf(t52_pre_topc, axiom,
% 0.89/1.12    (![A:$i]:
% 0.89/1.12     ( ( l1_pre_topc @ A ) =>
% 0.89/1.12       ( ![B:$i]:
% 0.89/1.12         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.12           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.89/1.12             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.89/1.12               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.89/1.12  thf('82', plain,
% 0.89/1.12      (![X39 : $i, X40 : $i]:
% 0.89/1.12         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.89/1.12          | ~ (v2_pre_topc @ X40)
% 0.89/1.12          | ((k2_pre_topc @ X40 @ X39) != (X39))
% 0.89/1.12          | (v4_pre_topc @ X39 @ X40)
% 0.89/1.12          | ~ (l1_pre_topc @ X40))),
% 0.89/1.12      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.89/1.12  thf('83', plain,
% 0.89/1.12      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.12        | (v4_pre_topc @ sk_B @ sk_A)
% 0.89/1.12        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.89/1.12        | ~ (v2_pre_topc @ sk_A))),
% 0.89/1.12      inference('sup-', [status(thm)], ['81', '82'])).
% 0.89/1.12  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.12  thf('86', plain,
% 0.89/1.12      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.89/1.12      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.89/1.12  thf('87', plain,
% 0.89/1.12      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('sup-', [status(thm)], ['80', '86'])).
% 0.89/1.12  thf('88', plain,
% 0.89/1.12      (((v4_pre_topc @ sk_B @ sk_A))
% 0.89/1.12         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.89/1.12      inference('simplify', [status(thm)], ['87'])).
% 0.89/1.12  thf('89', plain,
% 0.89/1.12      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.12      inference('split', [status(esa)], ['0'])).
% 0.89/1.12  thf('90', plain,
% 0.89/1.12      (~
% 0.89/1.12       (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.12          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.12             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.89/1.12       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.89/1.12      inference('sup-', [status(thm)], ['88', '89'])).
% 0.89/1.12  thf('91', plain, ($false),
% 0.89/1.12      inference('sat_resolution*', [status(thm)], ['1', '33', '34', '90'])).
% 0.89/1.12  
% 0.89/1.12  % SZS output end Refutation
% 0.89/1.12  
% 0.89/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
