%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S1vOkJr7ip

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:27 EST 2020

% Result     : Theorem 38.72s
% Output     : Refutation 38.72s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 727 expanded)
%              Number of leaves         :   46 ( 242 expanded)
%              Depth                    :   19
%              Number of atoms          : 2096 (7761 expanded)
%              Number of equality atoms :  153 ( 564 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_tarski @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['6','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('21',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 ) @ X55 )
      | ( v4_pre_topc @ X54 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('25',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('30',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','32'])).

thf('34',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

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

thf('38',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = X48 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('43',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k1_tops_1 @ X51 @ X50 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['46','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','31'])).

thf('55',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k2_tops_1 @ X53 @ X52 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X53 ) @ ( k2_pre_topc @ X53 @ X52 ) @ ( k1_tops_1 @ X53 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('62',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('79',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('80',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('81',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('84',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('85',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('86',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('87',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('88',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('89',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('93',plain,(
    ! [X23: $i] :
      ( ( k3_xboole_0 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('94',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('95',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('98',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('99',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('102',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','105'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('107',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('108',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('109',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('110',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) ) @ X29 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('115',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('116',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X15 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('117',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('118',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('119',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('120',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X17 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k5_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('123',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['114','124'])).

thf('126',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ ( k4_xboole_0 @ X28 @ X29 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) ) @ X29 ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('127',plain,(
    ! [X12: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('130',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['113','128','133'])).

thf('135',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('137',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k1_tops_1 @ X59 @ X58 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 @ ( k2_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('138',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k7_subset_1 @ X39 @ X38 @ X40 )
        = ( k4_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('144',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['135','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('146',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('147',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('151',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('153',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['144','153'])).

thf('155',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('156',plain,
    ( ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('158',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v2_pre_topc @ X49 )
      | ( ( k2_pre_topc @ X49 @ X48 )
       != X48 )
      | ( v4_pre_topc @ X48 @ X49 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('159',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ( ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
       != ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','162'])).

thf('164',plain,
    ( ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('166',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ~ ( v4_pre_topc @ X54 @ X55 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X55 ) @ X54 ) @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('167',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','31'])).

thf('170',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['164','170'])).

thf('172',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('173',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','74','75','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S1vOkJr7ip
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:36:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 38.72/38.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 38.72/38.97  % Solved by: fo/fo7.sh
% 38.72/38.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.72/38.97  % done 11951 iterations in 38.516s
% 38.72/38.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 38.72/38.97  % SZS output start Refutation
% 38.72/38.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 38.72/38.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 38.72/38.97  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 38.72/38.97  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 38.72/38.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 38.72/38.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 38.72/38.97  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 38.72/38.97  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 38.72/38.97  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 38.72/38.97  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 38.72/38.97  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 38.72/38.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 38.72/38.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 38.72/38.97  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 38.72/38.97  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 38.72/38.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 38.72/38.97  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 38.72/38.97  thf(sk_A_type, type, sk_A: $i).
% 38.72/38.97  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 38.72/38.97  thf(sk_B_type, type, sk_B: $i).
% 38.72/38.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 38.72/38.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 38.72/38.97  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 38.72/38.97  thf(t76_tops_1, conjecture,
% 38.72/38.97    (![A:$i]:
% 38.72/38.97     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 38.72/38.97       ( ![B:$i]:
% 38.72/38.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.72/38.97           ( ( v3_pre_topc @ B @ A ) <=>
% 38.72/38.97             ( ( k2_tops_1 @ A @ B ) =
% 38.72/38.97               ( k7_subset_1 @
% 38.72/38.97                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 38.72/38.97  thf(zf_stmt_0, negated_conjecture,
% 38.72/38.97    (~( ![A:$i]:
% 38.72/38.97        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 38.72/38.97          ( ![B:$i]:
% 38.72/38.97            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.72/38.97              ( ( v3_pre_topc @ B @ A ) <=>
% 38.72/38.97                ( ( k2_tops_1 @ A @ B ) =
% 38.72/38.97                  ( k7_subset_1 @
% 38.72/38.97                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 38.72/38.97    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 38.72/38.97  thf('0', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 38.72/38.97        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('1', plain,
% 38.72/38.97      (~
% 38.72/38.97       (((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 38.72/38.97       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 38.72/38.97      inference('split', [status(esa)], ['0'])).
% 38.72/38.97  thf('2', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 38.72/38.97        | (v3_pre_topc @ sk_B @ sk_A))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('3', plain,
% 38.72/38.97      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 38.72/38.97      inference('split', [status(esa)], ['2'])).
% 38.72/38.97  thf('4', plain,
% 38.72/38.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf(t3_subset, axiom,
% 38.72/38.97    (![A:$i,B:$i]:
% 38.72/38.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 38.72/38.97  thf('5', plain,
% 38.72/38.97      (![X43 : $i, X44 : $i]:
% 38.72/38.97         ((r1_tarski @ X43 @ X44) | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 38.72/38.97      inference('cnf', [status(esa)], [t3_subset])).
% 38.72/38.97  thf('6', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 38.72/38.97      inference('sup-', [status(thm)], ['4', '5'])).
% 38.72/38.97  thf(t28_xboole_1, axiom,
% 38.72/38.97    (![A:$i,B:$i]:
% 38.72/38.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 38.72/38.97  thf('7', plain,
% 38.72/38.97      (![X21 : $i, X22 : $i]:
% 38.72/38.97         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 38.72/38.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 38.72/38.97  thf(t12_setfam_1, axiom,
% 38.72/38.97    (![A:$i,B:$i]:
% 38.72/38.97     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 38.72/38.97  thf('8', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('9', plain,
% 38.72/38.97      (![X21 : $i, X22 : $i]:
% 38.72/38.97         (((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (X21))
% 38.72/38.97          | ~ (r1_tarski @ X21 @ X22))),
% 38.72/38.97      inference('demod', [status(thm)], ['7', '8'])).
% 38.72/38.97  thf('10', plain,
% 38.72/38.97      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 38.72/38.97      inference('sup-', [status(thm)], ['6', '9'])).
% 38.72/38.97  thf(commutativity_k2_tarski, axiom,
% 38.72/38.97    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 38.72/38.97  thf('11', plain,
% 38.72/38.97      (![X30 : $i, X31 : $i]:
% 38.72/38.97         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 38.72/38.97      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 38.72/38.97  thf(t100_xboole_1, axiom,
% 38.72/38.97    (![A:$i,B:$i]:
% 38.72/38.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 38.72/38.97  thf('12', plain,
% 38.72/38.97      (![X13 : $i, X14 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X13 @ X14)
% 38.72/38.97           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 38.72/38.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 38.72/38.97  thf('13', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('14', plain,
% 38.72/38.97      (![X13 : $i, X14 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X13 @ X14)
% 38.72/38.97           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 38.72/38.97      inference('demod', [status(thm)], ['12', '13'])).
% 38.72/38.97  thf('15', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X0 @ X1)
% 38.72/38.97           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 38.72/38.97      inference('sup+', [status(thm)], ['11', '14'])).
% 38.72/38.97  thf('16', plain,
% 38.72/38.97      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup+', [status(thm)], ['10', '15'])).
% 38.72/38.97  thf(t36_xboole_1, axiom,
% 38.72/38.97    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 38.72/38.97  thf('17', plain,
% 38.72/38.97      (![X24 : $i, X25 : $i]: (r1_tarski @ (k4_xboole_0 @ X24 @ X25) @ X24)),
% 38.72/38.97      inference('cnf', [status(esa)], [t36_xboole_1])).
% 38.72/38.97  thf('18', plain,
% 38.72/38.97      (![X43 : $i, X45 : $i]:
% 38.72/38.97         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 38.72/38.97      inference('cnf', [status(esa)], [t3_subset])).
% 38.72/38.97  thf('19', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['17', '18'])).
% 38.72/38.97  thf('20', plain,
% 38.72/38.97      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 38.72/38.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['16', '19'])).
% 38.72/38.97  thf(t29_tops_1, axiom,
% 38.72/38.97    (![A:$i]:
% 38.72/38.97     ( ( l1_pre_topc @ A ) =>
% 38.72/38.97       ( ![B:$i]:
% 38.72/38.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.72/38.97           ( ( v4_pre_topc @ B @ A ) <=>
% 38.72/38.97             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 38.72/38.97  thf('21', plain,
% 38.72/38.97      (![X54 : $i, X55 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 38.72/38.97          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X55) @ X54) @ X55)
% 38.72/38.97          | (v4_pre_topc @ X54 @ X55)
% 38.72/38.97          | ~ (l1_pre_topc @ X55))),
% 38.72/38.97      inference('cnf', [status(esa)], [t29_tops_1])).
% 38.72/38.97  thf('22', plain,
% 38.72/38.97      ((~ (l1_pre_topc @ sk_A)
% 38.72/38.97        | (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 38.72/38.97        | ~ (v3_pre_topc @ 
% 38.72/38.97             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97              (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 38.72/38.97             sk_A))),
% 38.72/38.97      inference('sup-', [status(thm)], ['20', '21'])).
% 38.72/38.97  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('24', plain,
% 38.72/38.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf(involutiveness_k3_subset_1, axiom,
% 38.72/38.97    (![A:$i,B:$i]:
% 38.72/38.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 38.72/38.97       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 38.72/38.97  thf('25', plain,
% 38.72/38.97      (![X36 : $i, X37 : $i]:
% 38.72/38.97         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 38.72/38.97          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 38.72/38.97      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 38.72/38.97  thf('26', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 38.72/38.97      inference('sup-', [status(thm)], ['24', '25'])).
% 38.72/38.97  thf('27', plain,
% 38.72/38.97      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup+', [status(thm)], ['10', '15'])).
% 38.72/38.97  thf('28', plain,
% 38.72/38.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf(d5_subset_1, axiom,
% 38.72/38.97    (![A:$i,B:$i]:
% 38.72/38.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 38.72/38.97       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 38.72/38.97  thf('29', plain,
% 38.72/38.97      (![X32 : $i, X33 : $i]:
% 38.72/38.97         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 38.72/38.97          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 38.72/38.97      inference('cnf', [status(esa)], [d5_subset_1])).
% 38.72/38.97  thf('30', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup-', [status(thm)], ['28', '29'])).
% 38.72/38.97  thf('31', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup+', [status(thm)], ['27', '30'])).
% 38.72/38.97  thf('32', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 38.72/38.97      inference('demod', [status(thm)], ['26', '31'])).
% 38.72/38.97  thf('33', plain,
% 38.72/38.97      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 38.72/38.97        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 38.72/38.97      inference('demod', [status(thm)], ['22', '23', '32'])).
% 38.72/38.97  thf('34', plain,
% 38.72/38.97      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 38.72/38.97         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 38.72/38.97      inference('sup-', [status(thm)], ['3', '33'])).
% 38.72/38.97  thf('35', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup-', [status(thm)], ['28', '29'])).
% 38.72/38.97  thf('36', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['17', '18'])).
% 38.72/38.97  thf('37', plain,
% 38.72/38.97      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 38.72/38.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['35', '36'])).
% 38.72/38.97  thf(t52_pre_topc, axiom,
% 38.72/38.97    (![A:$i]:
% 38.72/38.97     ( ( l1_pre_topc @ A ) =>
% 38.72/38.97       ( ![B:$i]:
% 38.72/38.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.72/38.97           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 38.72/38.97             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 38.72/38.97               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 38.72/38.97  thf('38', plain,
% 38.72/38.97      (![X48 : $i, X49 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 38.72/38.97          | ~ (v4_pre_topc @ X48 @ X49)
% 38.72/38.97          | ((k2_pre_topc @ X49 @ X48) = (X48))
% 38.72/38.97          | ~ (l1_pre_topc @ X49))),
% 38.72/38.97      inference('cnf', [status(esa)], [t52_pre_topc])).
% 38.72/38.97  thf('39', plain,
% 38.72/38.97      ((~ (l1_pre_topc @ sk_A)
% 38.72/38.97        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 38.72/38.97      inference('sup-', [status(thm)], ['37', '38'])).
% 38.72/38.97  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('41', plain,
% 38.72/38.97      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 38.72/38.97      inference('demod', [status(thm)], ['39', '40'])).
% 38.72/38.97  thf('42', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup+', [status(thm)], ['27', '30'])).
% 38.72/38.97  thf('43', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup+', [status(thm)], ['27', '30'])).
% 38.72/38.97  thf('44', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup+', [status(thm)], ['27', '30'])).
% 38.72/38.97  thf('45', plain,
% 38.72/38.97      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97        | ~ (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 38.72/38.97      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 38.72/38.97  thf('46', plain,
% 38.72/38.97      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 38.72/38.97         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 38.72/38.97      inference('sup-', [status(thm)], ['34', '45'])).
% 38.72/38.97  thf('47', plain,
% 38.72/38.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf(d1_tops_1, axiom,
% 38.72/38.97    (![A:$i]:
% 38.72/38.97     ( ( l1_pre_topc @ A ) =>
% 38.72/38.97       ( ![B:$i]:
% 38.72/38.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.72/38.97           ( ( k1_tops_1 @ A @ B ) =
% 38.72/38.97             ( k3_subset_1 @
% 38.72/38.97               ( u1_struct_0 @ A ) @ 
% 38.72/38.97               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 38.72/38.97  thf('48', plain,
% 38.72/38.97      (![X50 : $i, X51 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 38.72/38.97          | ((k1_tops_1 @ X51 @ X50)
% 38.72/38.97              = (k3_subset_1 @ (u1_struct_0 @ X51) @ 
% 38.72/38.97                 (k2_pre_topc @ X51 @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50))))
% 38.72/38.97          | ~ (l1_pre_topc @ X51))),
% 38.72/38.97      inference('cnf', [status(esa)], [d1_tops_1])).
% 38.72/38.97  thf('49', plain,
% 38.72/38.97      ((~ (l1_pre_topc @ sk_A)
% 38.72/38.97        | ((k1_tops_1 @ sk_A @ sk_B)
% 38.72/38.97            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97               (k2_pre_topc @ sk_A @ 
% 38.72/38.97                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 38.72/38.97      inference('sup-', [status(thm)], ['47', '48'])).
% 38.72/38.97  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('51', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup+', [status(thm)], ['27', '30'])).
% 38.72/38.97  thf('52', plain,
% 38.72/38.97      (((k1_tops_1 @ sk_A @ sk_B)
% 38.72/38.97         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 38.72/38.97      inference('demod', [status(thm)], ['49', '50', '51'])).
% 38.72/38.97  thf('53', plain,
% 38.72/38.97      ((((k1_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 38.72/38.97         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['46', '52'])).
% 38.72/38.97  thf('54', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 38.72/38.97      inference('demod', [status(thm)], ['26', '31'])).
% 38.72/38.97  thf('55', plain,
% 38.72/38.97      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 38.72/38.97         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['53', '54'])).
% 38.72/38.97  thf('56', plain,
% 38.72/38.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf(l78_tops_1, axiom,
% 38.72/38.97    (![A:$i]:
% 38.72/38.97     ( ( l1_pre_topc @ A ) =>
% 38.72/38.97       ( ![B:$i]:
% 38.72/38.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.72/38.97           ( ( k2_tops_1 @ A @ B ) =
% 38.72/38.97             ( k7_subset_1 @
% 38.72/38.97               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 38.72/38.97               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 38.72/38.97  thf('57', plain,
% 38.72/38.97      (![X52 : $i, X53 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 38.72/38.97          | ((k2_tops_1 @ X53 @ X52)
% 38.72/38.97              = (k7_subset_1 @ (u1_struct_0 @ X53) @ 
% 38.72/38.97                 (k2_pre_topc @ X53 @ X52) @ (k1_tops_1 @ X53 @ X52)))
% 38.72/38.97          | ~ (l1_pre_topc @ X53))),
% 38.72/38.97      inference('cnf', [status(esa)], [l78_tops_1])).
% 38.72/38.97  thf('58', plain,
% 38.72/38.97      ((~ (l1_pre_topc @ sk_A)
% 38.72/38.97        | ((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 38.72/38.97      inference('sup-', [status(thm)], ['56', '57'])).
% 38.72/38.97  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('60', plain,
% 38.72/38.97      (((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 38.72/38.97            (k1_tops_1 @ sk_A @ sk_B)))),
% 38.72/38.97      inference('demod', [status(thm)], ['58', '59'])).
% 38.72/38.97  thf('61', plain,
% 38.72/38.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf(dt_k2_pre_topc, axiom,
% 38.72/38.97    (![A:$i,B:$i]:
% 38.72/38.97     ( ( ( l1_pre_topc @ A ) & 
% 38.72/38.97         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 38.72/38.97       ( m1_subset_1 @
% 38.72/38.97         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 38.72/38.97  thf('62', plain,
% 38.72/38.97      (![X46 : $i, X47 : $i]:
% 38.72/38.97         (~ (l1_pre_topc @ X46)
% 38.72/38.97          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 38.72/38.97          | (m1_subset_1 @ (k2_pre_topc @ X46 @ X47) @ 
% 38.72/38.97             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 38.72/38.97      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 38.72/38.97  thf('63', plain,
% 38.72/38.97      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 38.72/38.97         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.72/38.97        | ~ (l1_pre_topc @ sk_A))),
% 38.72/38.97      inference('sup-', [status(thm)], ['61', '62'])).
% 38.72/38.97  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('65', plain,
% 38.72/38.97      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 38.72/38.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('demod', [status(thm)], ['63', '64'])).
% 38.72/38.97  thf(redefinition_k7_subset_1, axiom,
% 38.72/38.97    (![A:$i,B:$i,C:$i]:
% 38.72/38.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 38.72/38.97       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 38.72/38.97  thf('66', plain,
% 38.72/38.97      (![X38 : $i, X39 : $i, X40 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 38.72/38.97          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 38.72/38.97      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 38.72/38.97  thf('67', plain,
% 38.72/38.97      (![X0 : $i]:
% 38.72/38.97         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 38.72/38.97           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['65', '66'])).
% 38.72/38.97  thf('68', plain,
% 38.72/38.97      (((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 38.72/38.97            (k1_tops_1 @ sk_A @ sk_B)))),
% 38.72/38.97      inference('demod', [status(thm)], ['60', '67'])).
% 38.72/38.97  thf('69', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 38.72/38.97         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['55', '68'])).
% 38.72/38.97  thf('70', plain,
% 38.72/38.97      (![X0 : $i]:
% 38.72/38.97         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 38.72/38.97           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['65', '66'])).
% 38.72/38.97  thf('71', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 38.72/38.97         <= (~
% 38.72/38.97             (((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('split', [status(esa)], ['0'])).
% 38.72/38.97  thf('72', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 38.72/38.97         <= (~
% 38.72/38.97             (((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('sup-', [status(thm)], ['70', '71'])).
% 38.72/38.97  thf('73', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 38.72/38.97         <= (~
% 38.72/38.97             (((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 38.72/38.97             ((v3_pre_topc @ sk_B @ sk_A)))),
% 38.72/38.97      inference('sup-', [status(thm)], ['69', '72'])).
% 38.72/38.97  thf('74', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 38.72/38.97       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 38.72/38.97      inference('simplify', [status(thm)], ['73'])).
% 38.72/38.97  thf('75', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 38.72/38.97       ((v3_pre_topc @ sk_B @ sk_A))),
% 38.72/38.97      inference('split', [status(esa)], ['2'])).
% 38.72/38.97  thf('76', plain,
% 38.72/38.97      (![X0 : $i]:
% 38.72/38.97         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 38.72/38.97           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['65', '66'])).
% 38.72/38.97  thf('77', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('split', [status(esa)], ['2'])).
% 38.72/38.97  thf('78', plain,
% 38.72/38.97      ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('sup+', [status(thm)], ['76', '77'])).
% 38.72/38.97  thf(idempotence_k3_xboole_0, axiom,
% 38.72/38.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 38.72/38.97  thf('79', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 38.72/38.97      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 38.72/38.97  thf('80', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('81', plain,
% 38.72/38.97      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 38.72/38.97      inference('demod', [status(thm)], ['79', '80'])).
% 38.72/38.97  thf('82', plain,
% 38.72/38.97      (![X13 : $i, X14 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X13 @ X14)
% 38.72/38.97           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 38.72/38.97      inference('demod', [status(thm)], ['12', '13'])).
% 38.72/38.97  thf('83', plain,
% 38.72/38.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 38.72/38.97      inference('sup+', [status(thm)], ['81', '82'])).
% 38.72/38.97  thf(d4_xboole_0, axiom,
% 38.72/38.97    (![A:$i,B:$i,C:$i]:
% 38.72/38.97     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 38.72/38.97       ( ![D:$i]:
% 38.72/38.97         ( ( r2_hidden @ D @ C ) <=>
% 38.72/38.97           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 38.72/38.97  thf('84', plain,
% 38.72/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.72/38.97         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 38.72/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 38.72/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.72/38.97      inference('cnf', [status(esa)], [d4_xboole_0])).
% 38.72/38.97  thf('85', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('86', plain,
% 38.72/38.97      (![X1 : $i, X2 : $i, X5 : $i]:
% 38.72/38.97         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 38.72/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 38.72/38.97          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 38.72/38.97      inference('demod', [status(thm)], ['84', '85'])).
% 38.72/38.97  thf(t3_boole, axiom,
% 38.72/38.97    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 38.72/38.97  thf('87', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 38.72/38.97      inference('cnf', [status(esa)], [t3_boole])).
% 38.72/38.97  thf(d5_xboole_0, axiom,
% 38.72/38.97    (![A:$i,B:$i,C:$i]:
% 38.72/38.97     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 38.72/38.97       ( ![D:$i]:
% 38.72/38.97         ( ( r2_hidden @ D @ C ) <=>
% 38.72/38.97           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 38.72/38.97  thf('88', plain,
% 38.72/38.97      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 38.72/38.97         (~ (r2_hidden @ X10 @ X9)
% 38.72/38.97          | ~ (r2_hidden @ X10 @ X8)
% 38.72/38.97          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 38.72/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.72/38.97  thf('89', plain,
% 38.72/38.97      (![X7 : $i, X8 : $i, X10 : $i]:
% 38.72/38.97         (~ (r2_hidden @ X10 @ X8)
% 38.72/38.97          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 38.72/38.97      inference('simplify', [status(thm)], ['88'])).
% 38.72/38.97  thf('90', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['87', '89'])).
% 38.72/38.97  thf('91', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 38.72/38.97      inference('condensation', [status(thm)], ['90'])).
% 38.72/38.97  thf('92', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 38.72/38.97          | ((X1) = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0))))),
% 38.72/38.97      inference('sup-', [status(thm)], ['86', '91'])).
% 38.72/38.97  thf(t2_boole, axiom,
% 38.72/38.97    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 38.72/38.97  thf('93', plain,
% 38.72/38.97      (![X23 : $i]: ((k3_xboole_0 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 38.72/38.97      inference('cnf', [status(esa)], [t2_boole])).
% 38.72/38.97  thf('94', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('95', plain,
% 38.72/38.97      (![X23 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X23 @ k1_xboole_0)) = (k1_xboole_0))),
% 38.72/38.97      inference('demod', [status(thm)], ['93', '94'])).
% 38.72/38.97  thf('96', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 38.72/38.97          | ((X1) = (k1_xboole_0)))),
% 38.72/38.97      inference('demod', [status(thm)], ['92', '95'])).
% 38.72/38.97  thf('97', plain,
% 38.72/38.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 38.72/38.97      inference('sup+', [status(thm)], ['81', '82'])).
% 38.72/38.97  thf('98', plain,
% 38.72/38.97      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 38.72/38.97         (~ (r2_hidden @ X10 @ X9)
% 38.72/38.97          | (r2_hidden @ X10 @ X7)
% 38.72/38.97          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 38.72/38.97      inference('cnf', [status(esa)], [d5_xboole_0])).
% 38.72/38.97  thf('99', plain,
% 38.72/38.97      (![X7 : $i, X8 : $i, X10 : $i]:
% 38.72/38.97         ((r2_hidden @ X10 @ X7)
% 38.72/38.97          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 38.72/38.97      inference('simplify', [status(thm)], ['98'])).
% 38.72/38.97  thf('100', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['97', '99'])).
% 38.72/38.97  thf('101', plain,
% 38.72/38.97      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 38.72/38.97      inference('sup+', [status(thm)], ['81', '82'])).
% 38.72/38.97  thf('102', plain,
% 38.72/38.97      (![X7 : $i, X8 : $i, X10 : $i]:
% 38.72/38.97         (~ (r2_hidden @ X10 @ X8)
% 38.72/38.97          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 38.72/38.97      inference('simplify', [status(thm)], ['88'])).
% 38.72/38.97  thf('103', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 38.72/38.97          | ~ (r2_hidden @ X1 @ X0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['101', '102'])).
% 38.72/38.97  thf('104', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 38.72/38.97      inference('clc', [status(thm)], ['100', '103'])).
% 38.72/38.97  thf('105', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['96', '104'])).
% 38.72/38.97  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 38.72/38.97      inference('demod', [status(thm)], ['83', '105'])).
% 38.72/38.97  thf(t49_xboole_1, axiom,
% 38.72/38.97    (![A:$i,B:$i,C:$i]:
% 38.72/38.97     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 38.72/38.97       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 38.72/38.97  thf('107', plain,
% 38.72/38.97      (![X27 : $i, X28 : $i, X29 : $i]:
% 38.72/38.97         ((k3_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X29))
% 38.72/38.97           = (k4_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ X29))),
% 38.72/38.97      inference('cnf', [status(esa)], [t49_xboole_1])).
% 38.72/38.97  thf('108', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('109', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('110', plain,
% 38.72/38.97      (![X27 : $i, X28 : $i, X29 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X27 @ (k4_xboole_0 @ X28 @ X29)))
% 38.72/38.97           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X27 @ X28)) @ X29))),
% 38.72/38.97      inference('demod', [status(thm)], ['107', '108', '109'])).
% 38.72/38.97  thf('111', plain,
% 38.72/38.97      (![X13 : $i, X14 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X13 @ X14)
% 38.72/38.97           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 38.72/38.97      inference('demod', [status(thm)], ['12', '13'])).
% 38.72/38.97  thf('112', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 38.72/38.97           = (k5_xboole_0 @ X2 @ 
% 38.72/38.97              (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X1)) @ X0)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['110', '111'])).
% 38.72/38.97  thf('113', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X1 @ 
% 38.72/38.97           (k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 38.72/38.97           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 38.72/38.97      inference('sup+', [status(thm)], ['106', '112'])).
% 38.72/38.97  thf('114', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X0 @ X1)
% 38.72/38.97           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 38.72/38.97      inference('sup+', [status(thm)], ['11', '14'])).
% 38.72/38.97  thf('115', plain,
% 38.72/38.97      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 38.72/38.97      inference('demod', [status(thm)], ['79', '80'])).
% 38.72/38.97  thf(t112_xboole_1, axiom,
% 38.72/38.97    (![A:$i,B:$i,C:$i]:
% 38.72/38.97     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 38.72/38.97       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 38.72/38.97  thf('116', plain,
% 38.72/38.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 38.72/38.97         ((k5_xboole_0 @ (k3_xboole_0 @ X15 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 38.72/38.97           = (k3_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17))),
% 38.72/38.97      inference('cnf', [status(esa)], [t112_xboole_1])).
% 38.72/38.97  thf('117', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('118', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('119', plain,
% 38.72/38.97      (![X41 : $i, X42 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 38.72/38.97      inference('cnf', [status(esa)], [t12_setfam_1])).
% 38.72/38.97  thf('120', plain,
% 38.72/38.97      (![X15 : $i, X16 : $i, X17 : $i]:
% 38.72/38.97         ((k5_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X17)) @ 
% 38.72/38.97           (k1_setfam_1 @ (k2_tarski @ X16 @ X17)))
% 38.72/38.97           = (k1_setfam_1 @ (k2_tarski @ (k5_xboole_0 @ X15 @ X16) @ X17)))),
% 38.72/38.97      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 38.72/38.97  thf('121', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 38.72/38.97           = (k1_setfam_1 @ (k2_tarski @ (k5_xboole_0 @ X0 @ X1) @ X0)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['115', '120'])).
% 38.72/38.97  thf('122', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X0 @ X1)
% 38.72/38.97           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 38.72/38.97      inference('sup+', [status(thm)], ['11', '14'])).
% 38.72/38.97  thf('123', plain,
% 38.72/38.97      (![X30 : $i, X31 : $i]:
% 38.72/38.97         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 38.72/38.97      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 38.72/38.97  thf('124', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X0 @ X1)
% 38.72/38.97           = (k1_setfam_1 @ (k2_tarski @ X0 @ (k5_xboole_0 @ X0 @ X1))))),
% 38.72/38.97      inference('demod', [status(thm)], ['121', '122', '123'])).
% 38.72/38.97  thf('125', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 38.72/38.97           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 38.72/38.97      inference('sup+', [status(thm)], ['114', '124'])).
% 38.72/38.97  thf('126', plain,
% 38.72/38.97      (![X27 : $i, X28 : $i, X29 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X27 @ (k4_xboole_0 @ X28 @ X29)))
% 38.72/38.97           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X27 @ X28)) @ X29))),
% 38.72/38.97      inference('demod', [status(thm)], ['107', '108', '109'])).
% 38.72/38.97  thf('127', plain,
% 38.72/38.97      (![X12 : $i]: ((k1_setfam_1 @ (k2_tarski @ X12 @ X12)) = (X12))),
% 38.72/38.97      inference('demod', [status(thm)], ['79', '80'])).
% 38.72/38.97  thf('128', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 38.72/38.97           = (k4_xboole_0 @ X1 @ X0))),
% 38.72/38.97      inference('demod', [status(thm)], ['125', '126', '127'])).
% 38.72/38.97  thf('129', plain,
% 38.72/38.97      (![X23 : $i]:
% 38.72/38.97         ((k1_setfam_1 @ (k2_tarski @ X23 @ k1_xboole_0)) = (k1_xboole_0))),
% 38.72/38.97      inference('demod', [status(thm)], ['93', '94'])).
% 38.72/38.97  thf('130', plain,
% 38.72/38.97      (![X13 : $i, X14 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X13 @ X14)
% 38.72/38.97           = (k5_xboole_0 @ X13 @ (k1_setfam_1 @ (k2_tarski @ X13 @ X14))))),
% 38.72/38.97      inference('demod', [status(thm)], ['12', '13'])).
% 38.72/38.97  thf('131', plain,
% 38.72/38.97      (![X0 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 38.72/38.97      inference('sup+', [status(thm)], ['129', '130'])).
% 38.72/38.97  thf('132', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 38.72/38.97      inference('cnf', [status(esa)], [t3_boole])).
% 38.72/38.97  thf('133', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 38.72/38.97      inference('sup+', [status(thm)], ['131', '132'])).
% 38.72/38.97  thf('134', plain,
% 38.72/38.97      (![X0 : $i, X1 : $i]:
% 38.72/38.97         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 38.72/38.97      inference('demod', [status(thm)], ['113', '128', '133'])).
% 38.72/38.97  thf('135', plain,
% 38.72/38.97      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('sup+', [status(thm)], ['78', '134'])).
% 38.72/38.97  thf('136', plain,
% 38.72/38.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf(t74_tops_1, axiom,
% 38.72/38.97    (![A:$i]:
% 38.72/38.97     ( ( l1_pre_topc @ A ) =>
% 38.72/38.97       ( ![B:$i]:
% 38.72/38.97         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.72/38.97           ( ( k1_tops_1 @ A @ B ) =
% 38.72/38.97             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 38.72/38.97  thf('137', plain,
% 38.72/38.97      (![X58 : $i, X59 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 38.72/38.97          | ((k1_tops_1 @ X59 @ X58)
% 38.72/38.97              = (k7_subset_1 @ (u1_struct_0 @ X59) @ X58 @ 
% 38.72/38.97                 (k2_tops_1 @ X59 @ X58)))
% 38.72/38.97          | ~ (l1_pre_topc @ X59))),
% 38.72/38.97      inference('cnf', [status(esa)], [t74_tops_1])).
% 38.72/38.97  thf('138', plain,
% 38.72/38.97      ((~ (l1_pre_topc @ sk_A)
% 38.72/38.97        | ((k1_tops_1 @ sk_A @ sk_B)
% 38.72/38.97            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 38.72/38.97               (k2_tops_1 @ sk_A @ sk_B))))),
% 38.72/38.97      inference('sup-', [status(thm)], ['136', '137'])).
% 38.72/38.97  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('140', plain,
% 38.72/38.97      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('141', plain,
% 38.72/38.97      (![X38 : $i, X39 : $i, X40 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 38.72/38.97          | ((k7_subset_1 @ X39 @ X38 @ X40) = (k4_xboole_0 @ X38 @ X40)))),
% 38.72/38.97      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 38.72/38.97  thf('142', plain,
% 38.72/38.97      (![X0 : $i]:
% 38.72/38.97         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 38.72/38.97           = (k4_xboole_0 @ sk_B @ X0))),
% 38.72/38.97      inference('sup-', [status(thm)], ['140', '141'])).
% 38.72/38.97  thf('143', plain,
% 38.72/38.97      (((k1_tops_1 @ sk_A @ sk_B)
% 38.72/38.97         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 38.72/38.97      inference('demod', [status(thm)], ['138', '139', '142'])).
% 38.72/38.97  thf('144', plain,
% 38.72/38.97      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('sup+', [status(thm)], ['135', '143'])).
% 38.72/38.97  thf('145', plain,
% 38.72/38.97      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 38.72/38.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['16', '19'])).
% 38.72/38.97  thf('146', plain,
% 38.72/38.97      (![X46 : $i, X47 : $i]:
% 38.72/38.97         (~ (l1_pre_topc @ X46)
% 38.72/38.97          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 38.72/38.97          | (m1_subset_1 @ (k2_pre_topc @ X46 @ X47) @ 
% 38.72/38.97             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 38.72/38.97      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 38.72/38.97  thf('147', plain,
% 38.72/38.97      (((m1_subset_1 @ 
% 38.72/38.97         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 38.72/38.97         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 38.72/38.97        | ~ (l1_pre_topc @ sk_A))),
% 38.72/38.97      inference('sup-', [status(thm)], ['145', '146'])).
% 38.72/38.97  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('149', plain,
% 38.72/38.97      ((m1_subset_1 @ 
% 38.72/38.97        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 38.72/38.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('demod', [status(thm)], ['147', '148'])).
% 38.72/38.97  thf('150', plain,
% 38.72/38.97      (![X36 : $i, X37 : $i]:
% 38.72/38.97         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 38.72/38.97          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 38.72/38.97      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 38.72/38.97  thf('151', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97          (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 38.72/38.97         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 38.72/38.97      inference('sup-', [status(thm)], ['149', '150'])).
% 38.72/38.97  thf('152', plain,
% 38.72/38.97      (((k1_tops_1 @ sk_A @ sk_B)
% 38.72/38.97         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 38.72/38.97      inference('demod', [status(thm)], ['49', '50', '51'])).
% 38.72/38.97  thf('153', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 38.72/38.97         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 38.72/38.97      inference('demod', [status(thm)], ['151', '152'])).
% 38.72/38.97  thf('154', plain,
% 38.72/38.97      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('sup+', [status(thm)], ['144', '153'])).
% 38.72/38.97  thf('155', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 38.72/38.97      inference('sup+', [status(thm)], ['27', '30'])).
% 38.72/38.97  thf('156', plain,
% 38.72/38.97      ((((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97          = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('demod', [status(thm)], ['154', '155'])).
% 38.72/38.97  thf('157', plain,
% 38.72/38.97      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 38.72/38.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['16', '19'])).
% 38.72/38.97  thf('158', plain,
% 38.72/38.97      (![X48 : $i, X49 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 38.72/38.97          | ~ (v2_pre_topc @ X49)
% 38.72/38.97          | ((k2_pre_topc @ X49 @ X48) != (X48))
% 38.72/38.97          | (v4_pre_topc @ X48 @ X49)
% 38.72/38.97          | ~ (l1_pre_topc @ X49))),
% 38.72/38.97      inference('cnf', [status(esa)], [t52_pre_topc])).
% 38.72/38.97  thf('159', plain,
% 38.72/38.97      ((~ (l1_pre_topc @ sk_A)
% 38.72/38.97        | (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 38.72/38.97        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97            != (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97        | ~ (v2_pre_topc @ sk_A))),
% 38.72/38.97      inference('sup-', [status(thm)], ['157', '158'])).
% 38.72/38.97  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('161', plain, ((v2_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('162', plain,
% 38.72/38.97      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 38.72/38.97        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97            != (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 38.72/38.97      inference('demod', [status(thm)], ['159', '160', '161'])).
% 38.72/38.97  thf('163', plain,
% 38.72/38.97      (((((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 38.72/38.97           != (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 38.72/38.97         | (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('sup-', [status(thm)], ['156', '162'])).
% 38.72/38.97  thf('164', plain,
% 38.72/38.97      (((v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('simplify', [status(thm)], ['163'])).
% 38.72/38.97  thf('165', plain,
% 38.72/38.97      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 38.72/38.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 38.72/38.97      inference('sup+', [status(thm)], ['16', '19'])).
% 38.72/38.97  thf('166', plain,
% 38.72/38.97      (![X54 : $i, X55 : $i]:
% 38.72/38.97         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 38.72/38.97          | ~ (v4_pre_topc @ X54 @ X55)
% 38.72/38.97          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X55) @ X54) @ X55)
% 38.72/38.97          | ~ (l1_pre_topc @ X55))),
% 38.72/38.97      inference('cnf', [status(esa)], [t29_tops_1])).
% 38.72/38.97  thf('167', plain,
% 38.72/38.97      ((~ (l1_pre_topc @ sk_A)
% 38.72/38.97        | (v3_pre_topc @ 
% 38.72/38.97           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 38.72/38.97           sk_A)
% 38.72/38.97        | ~ (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 38.72/38.97      inference('sup-', [status(thm)], ['165', '166'])).
% 38.72/38.97  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 38.72/38.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.72/38.97  thf('169', plain,
% 38.72/38.97      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 38.72/38.97      inference('demod', [status(thm)], ['26', '31'])).
% 38.72/38.97  thf('170', plain,
% 38.72/38.97      (((v3_pre_topc @ sk_B @ sk_A)
% 38.72/38.97        | ~ (v4_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 38.72/38.97      inference('demod', [status(thm)], ['167', '168', '169'])).
% 38.72/38.97  thf('171', plain,
% 38.72/38.97      (((v3_pre_topc @ sk_B @ sk_A))
% 38.72/38.97         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 38.72/38.97      inference('sup-', [status(thm)], ['164', '170'])).
% 38.72/38.97  thf('172', plain,
% 38.72/38.97      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 38.72/38.97      inference('split', [status(esa)], ['0'])).
% 38.72/38.97  thf('173', plain,
% 38.72/38.97      (~
% 38.72/38.97       (((k2_tops_1 @ sk_A @ sk_B)
% 38.72/38.97          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 38.72/38.97             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 38.72/38.97       ((v3_pre_topc @ sk_B @ sk_A))),
% 38.72/38.97      inference('sup-', [status(thm)], ['171', '172'])).
% 38.72/38.97  thf('174', plain, ($false),
% 38.72/38.97      inference('sat_resolution*', [status(thm)], ['1', '74', '75', '173'])).
% 38.72/38.97  
% 38.72/38.97  % SZS output end Refutation
% 38.72/38.97  
% 38.72/38.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
