%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ck6kemOt5H

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:14 EST 2020

% Result     : Theorem 5.41s
% Output     : Refutation 5.41s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 237 expanded)
%              Number of leaves         :   31 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  669 (2091 expanded)
%              Number of equality atoms :   46 ( 149 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k6_subset_1 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['3','8'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k6_subset_1 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ ( k6_subset_1 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k6_subset_1 @ X23 @ ( k6_subset_1 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('24',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['9','17'])).

thf('26',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( l1_pre_topc @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X53 @ X54 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( ( k2_pre_topc @ X58 @ X57 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X58 ) @ X57 @ ( k2_tops_1 @ X58 @ X57 ) ) )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ~ ( v4_pre_topc @ X51 @ X52 )
      | ( ( k2_pre_topc @ X52 @ X51 )
        = X51 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','46'])).

thf('48',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('49',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','47','48'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X13 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('54',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('55',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ X22 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ck6kemOt5H
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 5.41/5.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.41/5.61  % Solved by: fo/fo7.sh
% 5.41/5.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.41/5.61  % done 12122 iterations in 5.149s
% 5.41/5.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.41/5.61  % SZS output start Refutation
% 5.41/5.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.41/5.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.41/5.61  thf(sk_B_type, type, sk_B: $i).
% 5.41/5.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.41/5.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.41/5.61  thf(sk_A_type, type, sk_A: $i).
% 5.41/5.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.41/5.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.41/5.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.41/5.61  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.41/5.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.41/5.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.41/5.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.41/5.61  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 5.41/5.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.41/5.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.41/5.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.41/5.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.41/5.61  thf(t69_tops_1, conjecture,
% 5.41/5.61    (![A:$i]:
% 5.41/5.61     ( ( l1_pre_topc @ A ) =>
% 5.41/5.61       ( ![B:$i]:
% 5.41/5.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.41/5.61           ( ( v4_pre_topc @ B @ A ) =>
% 5.41/5.61             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 5.41/5.61  thf(zf_stmt_0, negated_conjecture,
% 5.41/5.61    (~( ![A:$i]:
% 5.41/5.61        ( ( l1_pre_topc @ A ) =>
% 5.41/5.61          ( ![B:$i]:
% 5.41/5.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.41/5.61              ( ( v4_pre_topc @ B @ A ) =>
% 5.41/5.61                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 5.41/5.61    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 5.41/5.61  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf('1', plain,
% 5.41/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf(involutiveness_k3_subset_1, axiom,
% 5.41/5.61    (![A:$i,B:$i]:
% 5.41/5.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.41/5.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 5.41/5.61  thf('2', plain,
% 5.41/5.61      (![X37 : $i, X38 : $i]:
% 5.41/5.61         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 5.41/5.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 5.41/5.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 5.41/5.61  thf('3', plain,
% 5.41/5.61      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.41/5.61         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 5.41/5.61      inference('sup-', [status(thm)], ['1', '2'])).
% 5.41/5.61  thf('4', plain,
% 5.41/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf(d5_subset_1, axiom,
% 5.41/5.61    (![A:$i,B:$i]:
% 5.41/5.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.41/5.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.41/5.61  thf('5', plain,
% 5.41/5.61      (![X31 : $i, X32 : $i]:
% 5.41/5.61         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 5.41/5.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 5.41/5.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.41/5.61  thf(redefinition_k6_subset_1, axiom,
% 5.41/5.61    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 5.41/5.61  thf('6', plain,
% 5.41/5.61      (![X42 : $i, X43 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 5.41/5.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.41/5.61  thf('7', plain,
% 5.41/5.61      (![X31 : $i, X32 : $i]:
% 5.41/5.61         (((k3_subset_1 @ X31 @ X32) = (k6_subset_1 @ X31 @ X32))
% 5.41/5.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 5.41/5.61      inference('demod', [status(thm)], ['5', '6'])).
% 5.41/5.61  thf('8', plain,
% 5.41/5.61      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.41/5.61         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.41/5.61      inference('sup-', [status(thm)], ['4', '7'])).
% 5.41/5.61  thf('9', plain,
% 5.41/5.61      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.41/5.61         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 5.41/5.61      inference('demod', [status(thm)], ['3', '8'])).
% 5.41/5.61  thf(dt_k6_subset_1, axiom,
% 5.41/5.61    (![A:$i,B:$i]:
% 5.41/5.61     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.41/5.61  thf('10', plain,
% 5.41/5.61      (![X35 : $i, X36 : $i]:
% 5.41/5.61         (m1_subset_1 @ (k6_subset_1 @ X35 @ X36) @ (k1_zfmisc_1 @ X35))),
% 5.41/5.61      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 5.41/5.61  thf('11', plain,
% 5.41/5.61      (![X31 : $i, X32 : $i]:
% 5.41/5.61         (((k3_subset_1 @ X31 @ X32) = (k6_subset_1 @ X31 @ X32))
% 5.41/5.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 5.41/5.61      inference('demod', [status(thm)], ['5', '6'])).
% 5.41/5.61  thf('12', plain,
% 5.41/5.61      (![X0 : $i, X1 : $i]:
% 5.41/5.61         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 5.41/5.61           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 5.41/5.61      inference('sup-', [status(thm)], ['10', '11'])).
% 5.41/5.61  thf(t48_xboole_1, axiom,
% 5.41/5.61    (![A:$i,B:$i]:
% 5.41/5.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.41/5.61  thf('13', plain,
% 5.41/5.61      (![X23 : $i, X24 : $i]:
% 5.41/5.61         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 5.41/5.61           = (k3_xboole_0 @ X23 @ X24))),
% 5.41/5.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.41/5.61  thf('14', plain,
% 5.41/5.61      (![X42 : $i, X43 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 5.41/5.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.41/5.61  thf('15', plain,
% 5.41/5.61      (![X42 : $i, X43 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 5.41/5.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.41/5.61  thf('16', plain,
% 5.41/5.61      (![X23 : $i, X24 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X23 @ (k6_subset_1 @ X23 @ X24))
% 5.41/5.61           = (k3_xboole_0 @ X23 @ X24))),
% 5.41/5.61      inference('demod', [status(thm)], ['13', '14', '15'])).
% 5.41/5.61  thf('17', plain,
% 5.41/5.61      (![X0 : $i, X1 : $i]:
% 5.41/5.61         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 5.41/5.61           = (k3_xboole_0 @ X0 @ X1))),
% 5.41/5.61      inference('demod', [status(thm)], ['12', '16'])).
% 5.41/5.61  thf('18', plain, (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 5.41/5.61      inference('demod', [status(thm)], ['9', '17'])).
% 5.41/5.61  thf(t100_xboole_1, axiom,
% 5.41/5.61    (![A:$i,B:$i]:
% 5.41/5.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.41/5.61  thf('19', plain,
% 5.41/5.61      (![X4 : $i, X5 : $i]:
% 5.41/5.61         ((k4_xboole_0 @ X4 @ X5)
% 5.41/5.61           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 5.41/5.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.41/5.61  thf('20', plain,
% 5.41/5.61      (![X42 : $i, X43 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 5.41/5.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.41/5.61  thf('21', plain,
% 5.41/5.61      (![X4 : $i, X5 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X4 @ X5)
% 5.41/5.61           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 5.41/5.61      inference('demod', [status(thm)], ['19', '20'])).
% 5.41/5.61  thf('22', plain,
% 5.41/5.61      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.41/5.61         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.41/5.61      inference('sup+', [status(thm)], ['18', '21'])).
% 5.41/5.61  thf('23', plain,
% 5.41/5.61      (![X23 : $i, X24 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X23 @ (k6_subset_1 @ X23 @ X24))
% 5.41/5.61           = (k3_xboole_0 @ X23 @ X24))),
% 5.41/5.61      inference('demod', [status(thm)], ['13', '14', '15'])).
% 5.41/5.61  thf('24', plain,
% 5.41/5.61      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.41/5.61         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 5.41/5.61         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.41/5.61      inference('sup+', [status(thm)], ['22', '23'])).
% 5.41/5.61  thf('25', plain, (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 5.41/5.61      inference('demod', [status(thm)], ['9', '17'])).
% 5.41/5.61  thf('26', plain,
% 5.41/5.61      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.41/5.61         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 5.41/5.61      inference('demod', [status(thm)], ['24', '25'])).
% 5.41/5.61  thf('27', plain,
% 5.41/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf(dt_k2_tops_1, axiom,
% 5.41/5.61    (![A:$i,B:$i]:
% 5.41/5.61     ( ( ( l1_pre_topc @ A ) & 
% 5.41/5.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.41/5.61       ( m1_subset_1 @
% 5.41/5.61         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.41/5.61  thf('28', plain,
% 5.41/5.61      (![X53 : $i, X54 : $i]:
% 5.41/5.61         (~ (l1_pre_topc @ X53)
% 5.41/5.61          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 5.41/5.61          | (m1_subset_1 @ (k2_tops_1 @ X53 @ X54) @ 
% 5.41/5.61             (k1_zfmisc_1 @ (u1_struct_0 @ X53))))),
% 5.41/5.61      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 5.41/5.61  thf('29', plain,
% 5.41/5.61      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.41/5.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.41/5.61        | ~ (l1_pre_topc @ sk_A))),
% 5.41/5.61      inference('sup-', [status(thm)], ['27', '28'])).
% 5.41/5.61  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf('31', plain,
% 5.41/5.61      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.41/5.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.41/5.61      inference('demod', [status(thm)], ['29', '30'])).
% 5.41/5.61  thf('32', plain,
% 5.41/5.61      (![X35 : $i, X36 : $i]:
% 5.41/5.61         (m1_subset_1 @ (k6_subset_1 @ X35 @ X36) @ (k1_zfmisc_1 @ X35))),
% 5.41/5.61      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 5.41/5.61  thf(redefinition_k4_subset_1, axiom,
% 5.41/5.61    (![A:$i,B:$i,C:$i]:
% 5.41/5.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.41/5.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.41/5.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.41/5.61  thf('33', plain,
% 5.41/5.61      (![X39 : $i, X40 : $i, X41 : $i]:
% 5.41/5.61         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 5.41/5.61          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 5.41/5.61          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 5.41/5.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.41/5.61  thf('34', plain,
% 5.41/5.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.41/5.61         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 5.41/5.61            = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2))
% 5.41/5.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 5.41/5.61      inference('sup-', [status(thm)], ['32', '33'])).
% 5.41/5.61  thf('35', plain,
% 5.41/5.61      (![X0 : $i]:
% 5.41/5.61         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.41/5.61           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 5.41/5.61           (k2_tops_1 @ sk_A @ sk_B))
% 5.41/5.61           = (k2_xboole_0 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 5.41/5.61              (k2_tops_1 @ sk_A @ sk_B)))),
% 5.41/5.61      inference('sup-', [status(thm)], ['31', '34'])).
% 5.41/5.61  thf('36', plain,
% 5.41/5.61      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 5.41/5.61         = (k2_xboole_0 @ 
% 5.41/5.61            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.41/5.61             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 5.41/5.61            (k2_tops_1 @ sk_A @ sk_B)))),
% 5.41/5.61      inference('sup+', [status(thm)], ['26', '35'])).
% 5.41/5.61  thf('37', plain,
% 5.41/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf(t65_tops_1, axiom,
% 5.41/5.61    (![A:$i]:
% 5.41/5.61     ( ( l1_pre_topc @ A ) =>
% 5.41/5.61       ( ![B:$i]:
% 5.41/5.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.41/5.61           ( ( k2_pre_topc @ A @ B ) =
% 5.41/5.61             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.41/5.61  thf('38', plain,
% 5.41/5.61      (![X57 : $i, X58 : $i]:
% 5.41/5.61         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 5.41/5.61          | ((k2_pre_topc @ X58 @ X57)
% 5.41/5.61              = (k4_subset_1 @ (u1_struct_0 @ X58) @ X57 @ 
% 5.41/5.61                 (k2_tops_1 @ X58 @ X57)))
% 5.41/5.61          | ~ (l1_pre_topc @ X58))),
% 5.41/5.61      inference('cnf', [status(esa)], [t65_tops_1])).
% 5.41/5.61  thf('39', plain,
% 5.41/5.61      ((~ (l1_pre_topc @ sk_A)
% 5.41/5.61        | ((k2_pre_topc @ sk_A @ sk_B)
% 5.41/5.61            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.41/5.61               (k2_tops_1 @ sk_A @ sk_B))))),
% 5.41/5.61      inference('sup-', [status(thm)], ['37', '38'])).
% 5.41/5.61  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf('41', plain,
% 5.41/5.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf(t52_pre_topc, axiom,
% 5.41/5.61    (![A:$i]:
% 5.41/5.61     ( ( l1_pre_topc @ A ) =>
% 5.41/5.61       ( ![B:$i]:
% 5.41/5.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.41/5.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 5.41/5.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 5.41/5.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 5.41/5.61  thf('42', plain,
% 5.41/5.61      (![X51 : $i, X52 : $i]:
% 5.41/5.61         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 5.41/5.61          | ~ (v4_pre_topc @ X51 @ X52)
% 5.41/5.61          | ((k2_pre_topc @ X52 @ X51) = (X51))
% 5.41/5.61          | ~ (l1_pre_topc @ X52))),
% 5.41/5.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 5.41/5.61  thf('43', plain,
% 5.41/5.61      ((~ (l1_pre_topc @ sk_A)
% 5.41/5.61        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 5.41/5.61        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.41/5.61      inference('sup-', [status(thm)], ['41', '42'])).
% 5.41/5.61  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf('45', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 5.41/5.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.41/5.61  thf('46', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 5.41/5.61      inference('demod', [status(thm)], ['43', '44', '45'])).
% 5.41/5.61  thf('47', plain,
% 5.41/5.61      (((sk_B)
% 5.41/5.61         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.41/5.61            (k2_tops_1 @ sk_A @ sk_B)))),
% 5.41/5.61      inference('demod', [status(thm)], ['39', '40', '46'])).
% 5.41/5.61  thf('48', plain,
% 5.41/5.61      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.41/5.61         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 5.41/5.61      inference('demod', [status(thm)], ['24', '25'])).
% 5.41/5.61  thf('49', plain,
% 5.41/5.61      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.41/5.61      inference('demod', [status(thm)], ['36', '47', '48'])).
% 5.41/5.61  thf(t36_xboole_1, axiom,
% 5.41/5.61    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.41/5.61  thf('50', plain,
% 5.41/5.61      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 5.41/5.61      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.41/5.61  thf('51', plain,
% 5.41/5.61      (![X42 : $i, X43 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 5.41/5.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.41/5.61  thf('52', plain,
% 5.41/5.61      (![X13 : $i, X14 : $i]: (r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X13)),
% 5.41/5.61      inference('demod', [status(thm)], ['50', '51'])).
% 5.41/5.61  thf(t44_xboole_1, axiom,
% 5.41/5.61    (![A:$i,B:$i,C:$i]:
% 5.41/5.61     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 5.41/5.61       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.41/5.61  thf('53', plain,
% 5.41/5.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.41/5.61         ((r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 5.41/5.61          | ~ (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22))),
% 5.41/5.61      inference('cnf', [status(esa)], [t44_xboole_1])).
% 5.41/5.61  thf('54', plain,
% 5.41/5.61      (![X42 : $i, X43 : $i]:
% 5.41/5.61         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 5.41/5.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 5.41/5.61  thf('55', plain,
% 5.41/5.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.41/5.61         ((r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 5.41/5.61          | ~ (r1_tarski @ (k6_subset_1 @ X20 @ X21) @ X22))),
% 5.41/5.61      inference('demod', [status(thm)], ['53', '54'])).
% 5.41/5.61  thf('56', plain,
% 5.41/5.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.41/5.61      inference('sup-', [status(thm)], ['52', '55'])).
% 5.41/5.61  thf('57', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.41/5.61      inference('sup+', [status(thm)], ['49', '56'])).
% 5.41/5.61  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 5.41/5.61  
% 5.41/5.61  % SZS output end Refutation
% 5.41/5.61  
% 5.44/5.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
