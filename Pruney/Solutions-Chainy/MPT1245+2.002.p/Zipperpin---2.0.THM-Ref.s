%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aSwuSrhEYr

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:10 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 235 expanded)
%              Number of leaves         :   31 (  85 expanded)
%              Depth                    :   11
%              Number of atoms          :  722 (2588 expanded)
%              Number of equality atoms :   41 ( 134 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t59_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
              = ( k2_pre_topc @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
                = ( k2_pre_topc @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t59_tops_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(t58_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) )
            = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_pre_topc @ X44 @ ( k1_tops_1 @ X44 @ X43 ) )
        = ( k2_pre_topc @ X44 @ ( k1_tops_1 @ X44 @ ( k2_pre_topc @ X44 @ ( k1_tops_1 @ X44 @ X43 ) ) ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t58_tops_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k1_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) )
        = ( k2_pre_topc @ X0 @ ( k1_tops_1 @ X0 @ ( k2_pre_topc @ X0 @ ( k1_tops_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 ) ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('31',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('33',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v4_pre_topc @ X37 @ X38 )
      | ( ( k2_pre_topc @ X38 @ X37 )
        = X37 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('39',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 ) @ X42 )
      | ( v4_pre_topc @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X28 @ ( k3_subset_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['40','41','44','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('48',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['35','46','47','48','49'])).

thf('51',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','50'])).

thf('52',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('53',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','53','54','55'])).

thf('57',plain,(
    ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
 != ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aSwuSrhEYr
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:27:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 1056 iterations in 0.310s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.58/0.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.77  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.58/0.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.77  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.77  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.58/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.58/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(t79_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.58/0.77      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.77  thf(symmetry_r1_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      (![X6 : $i, X7 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.58/0.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.77  thf(t59_tops_1, conjecture,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77           ( ( v3_pre_topc @ B @ A ) =>
% 0.58/0.77             ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) =
% 0.58/0.77               ( k2_pre_topc @ A @ B ) ) ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i]:
% 0.58/0.77        ( ( l1_pre_topc @ A ) =>
% 0.58/0.77          ( ![B:$i]:
% 0.58/0.77            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77              ( ( v3_pre_topc @ B @ A ) =>
% 0.58/0.77                ( ( k2_pre_topc @
% 0.58/0.77                    A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) =
% 0.58/0.77                  ( k2_pre_topc @ A @ B ) ) ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t59_tops_1])).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t3_subset, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (![X34 : $i, X35 : $i]:
% 0.58/0.77         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.77  thf('5', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.77  thf(t63_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.58/0.77       ( r1_xboole_0 @ A @ C ) ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X15 @ X16)
% 0.58/0.77          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.58/0.77          | (r1_xboole_0 @ X15 @ X17))),
% 0.58/0.77      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ sk_B @ X0)
% 0.58/0.77          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['2', '7'])).
% 0.58/0.77  thf(t83_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 0.58/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))
% 0.58/0.77           = (sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['8', '9'])).
% 0.58/0.77  thf(t48_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X13 : $i, X14 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.58/0.77           = (k3_xboole_0 @ X13 @ X14))),
% 0.58/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.77  thf('12', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['10', '11'])).
% 0.58/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.58/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      (![X13 : $i, X14 : $i]:
% 0.58/0.77         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.58/0.77           = (k3_xboole_0 @ X13 @ X14))),
% 0.58/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.58/0.77  thf(t36_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.58/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X34 : $i, X36 : $i]:
% 0.58/0.77         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.58/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.58/0.77      inference('sup+', [status(thm)], ['14', '17'])).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.77      inference('sup+', [status(thm)], ['13', '18'])).
% 0.58/0.77  thf(t58_tops_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77           ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.58/0.77             ( k2_pre_topc @
% 0.58/0.77               A @ 
% 0.58/0.77               ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      (![X43 : $i, X44 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.58/0.77          | ((k2_pre_topc @ X44 @ (k1_tops_1 @ X44 @ X43))
% 0.58/0.77              = (k2_pre_topc @ X44 @ 
% 0.58/0.77                 (k1_tops_1 @ X44 @ 
% 0.58/0.77                  (k2_pre_topc @ X44 @ (k1_tops_1 @ X44 @ X43)))))
% 0.58/0.77          | ~ (l1_pre_topc @ X44))),
% 0.58/0.77      inference('cnf', [status(esa)], [t58_tops_1])).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (l1_pre_topc @ X0)
% 0.58/0.77          | ((k2_pre_topc @ X0 @ 
% 0.58/0.77              (k1_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))
% 0.58/0.77              = (k2_pre_topc @ X0 @ 
% 0.58/0.77                 (k1_tops_1 @ X0 @ 
% 0.58/0.77                  (k2_pre_topc @ X0 @ 
% 0.58/0.77                   (k1_tops_1 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      ((((k2_pre_topc @ sk_A @ 
% 0.58/0.77          (k1_tops_1 @ sk_A @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.58/0.77          = (k2_pre_topc @ sk_A @ 
% 0.58/0.77             (k1_tops_1 @ sk_A @ 
% 0.58/0.77              (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))
% 0.58/0.77        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.77      inference('sup+', [status(thm)], ['12', '21'])).
% 0.58/0.77  thf('23', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['10', '11'])).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(d1_tops_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77           ( ( k1_tops_1 @ A @ B ) =
% 0.58/0.77             ( k3_subset_1 @
% 0.58/0.77               ( u1_struct_0 @ A ) @ 
% 0.58/0.77               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.58/0.77  thf('25', plain,
% 0.58/0.77      (![X39 : $i, X40 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.58/0.77          | ((k1_tops_1 @ X40 @ X39)
% 0.58/0.77              = (k3_subset_1 @ (u1_struct_0 @ X40) @ 
% 0.58/0.77                 (k2_pre_topc @ X40 @ (k3_subset_1 @ (u1_struct_0 @ X40) @ X39))))
% 0.58/0.77          | ~ (l1_pre_topc @ X40))),
% 0.58/0.77      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.77        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.77            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77               (k2_pre_topc @ sk_A @ 
% 0.58/0.77                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.77  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.77         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['26', '27'])).
% 0.58/0.77  thf('29', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(d5_subset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.77       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X25 : $i, X26 : $i]:
% 0.58/0.77         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.58/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.58/0.77         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.77  thf(t52_pre_topc, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.58/0.77             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.58/0.77               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      (![X37 : $i, X38 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.58/0.77          | ~ (v4_pre_topc @ X37 @ X38)
% 0.58/0.77          | ((k2_pre_topc @ X38 @ X37) = (X37))
% 0.58/0.77          | ~ (l1_pre_topc @ X38))),
% 0.58/0.77      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (l1_pre_topc @ X0)
% 0.58/0.77          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.58/0.77              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.58/0.77          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('35', plain,
% 0.58/0.77      ((~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.58/0.77        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.77            = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.77        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['31', '34'])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.58/0.77         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.58/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('sup+', [status(thm)], ['36', '37'])).
% 0.58/0.77  thf(t29_tops_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( l1_pre_topc @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.77           ( ( v4_pre_topc @ B @ A ) <=>
% 0.58/0.77             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      (![X41 : $i, X42 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.58/0.77          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X42) @ X41) @ X42)
% 0.58/0.77          | (v4_pre_topc @ X41 @ X42)
% 0.58/0.77          | ~ (l1_pre_topc @ X42))),
% 0.58/0.77      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.58/0.77  thf('40', plain,
% 0.58/0.77      ((~ (l1_pre_topc @ sk_A)
% 0.58/0.77        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.58/0.77        | ~ (v3_pre_topc @ 
% 0.58/0.77             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.58/0.77             sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.77  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(involutiveness_k3_subset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.77       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.58/0.77  thf('43', plain,
% 0.58/0.77      (![X27 : $i, X28 : $i]:
% 0.58/0.77         (((k3_subset_1 @ X28 @ (k3_subset_1 @ X28 @ X27)) = (X27))
% 0.58/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.58/0.77      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.58/0.77  thf('44', plain,
% 0.58/0.77      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.77  thf('45', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('46', plain,
% 0.58/0.77      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.58/0.77      inference('demod', [status(thm)], ['40', '41', '44', '45'])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.58/0.77         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('48', plain,
% 0.58/0.77      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.58/0.77         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.58/0.77         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['35', '46', '47', '48', '49'])).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      (((k1_tops_1 @ sk_A @ sk_B)
% 0.58/0.77         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.58/0.77      inference('demod', [status(thm)], ['28', '50'])).
% 0.58/0.77  thf('52', plain,
% 0.58/0.77      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.58/0.77         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.77  thf('53', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.58/0.77      inference('sup+', [status(thm)], ['51', '52'])).
% 0.58/0.77  thf('54', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.58/0.77      inference('sup+', [status(thm)], ['51', '52'])).
% 0.58/0.77  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      (((k2_pre_topc @ sk_A @ sk_B)
% 0.58/0.77         = (k2_pre_topc @ sk_A @ 
% 0.58/0.77            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.58/0.77      inference('demod', [status(thm)], ['22', '23', '53', '54', '55'])).
% 0.58/0.77  thf('57', plain,
% 0.58/0.77      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.58/0.77         != (k2_pre_topc @ sk_A @ sk_B))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('58', plain, ($false),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
