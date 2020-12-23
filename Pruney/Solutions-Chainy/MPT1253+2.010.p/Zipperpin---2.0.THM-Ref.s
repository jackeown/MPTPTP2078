%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o5s2UqYBY5

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:14 EST 2020

% Result     : Theorem 20.45s
% Output     : Refutation 20.45s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 876 expanded)
%              Number of leaves         :   43 ( 299 expanded)
%              Depth                    :   21
%              Number of atoms          : 1752 (6836 expanded)
%              Number of equality atoms :  114 ( 456 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X48: $i,X50: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['5','10','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X48: $i,X50: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('63',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X28 @ X29 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','72'])).

thf('74',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['47','80'])).

thf('82',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('83',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('84',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['34','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('87',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( l1_pre_topc @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X51 @ X52 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('92',plain,(
    ! [X48: $i,X50: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('94',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['85','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('101',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k2_pre_topc @ X59 @ X58 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 @ ( k2_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['34','84'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('107',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('110',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('111',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('112',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['109','118'])).

thf('120',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('125',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('128',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('129',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('136',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('137',plain,(
    ! [X48: $i,X50: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('138',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('139',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X35 @ X34 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('143',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('144',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['141','146'])).

thf('148',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('151',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['134','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['108','157'])).

thf('159',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['107','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('162',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v4_pre_topc @ X53 @ X54 )
      | ~ ( r1_tarski @ X55 @ X53 )
      | ( r1_tarski @ ( k2_pre_topc @ X54 @ X55 ) @ X53 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('169',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X48: $i,X50: $i] :
      ( ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X50 ) )
      | ~ ( r1_tarski @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('171',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('173',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_B @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('175',plain,(
    r1_tarski @ ( k4_subset_1 @ sk_B @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('178',plain,
    ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['175','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('181',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('183',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','181','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('185',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    $false ),
    inference(demod,[status(thm)],['0','185'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o5s2UqYBY5
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:06:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 20.45/20.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 20.45/20.66  % Solved by: fo/fo7.sh
% 20.45/20.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.45/20.66  % done 26965 iterations in 20.203s
% 20.45/20.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 20.45/20.66  % SZS output start Refutation
% 20.45/20.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 20.45/20.66  thf(sk_B_type, type, sk_B: $i).
% 20.45/20.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 20.45/20.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 20.45/20.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 20.45/20.66  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 20.45/20.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 20.45/20.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 20.45/20.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 20.45/20.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 20.45/20.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 20.45/20.66  thf(sk_A_type, type, sk_A: $i).
% 20.45/20.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.45/20.66  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 20.45/20.66  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 20.45/20.66  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 20.45/20.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.45/20.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.45/20.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 20.45/20.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.45/20.66  thf(t69_tops_1, conjecture,
% 20.45/20.66    (![A:$i]:
% 20.45/20.66     ( ( l1_pre_topc @ A ) =>
% 20.45/20.66       ( ![B:$i]:
% 20.45/20.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.45/20.66           ( ( v4_pre_topc @ B @ A ) =>
% 20.45/20.66             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 20.45/20.66  thf(zf_stmt_0, negated_conjecture,
% 20.45/20.66    (~( ![A:$i]:
% 20.45/20.66        ( ( l1_pre_topc @ A ) =>
% 20.45/20.66          ( ![B:$i]:
% 20.45/20.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.45/20.66              ( ( v4_pre_topc @ B @ A ) =>
% 20.45/20.66                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 20.45/20.66    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 20.45/20.66  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 20.45/20.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.66  thf('1', plain,
% 20.45/20.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.66  thf(d5_subset_1, axiom,
% 20.45/20.66    (![A:$i,B:$i]:
% 20.45/20.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 20.45/20.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 20.45/20.66  thf('2', plain,
% 20.45/20.66      (![X30 : $i, X31 : $i]:
% 20.45/20.66         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 20.45/20.66          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 20.45/20.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 20.45/20.66  thf('3', plain,
% 20.45/20.66      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 20.45/20.66         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 20.45/20.66      inference('sup-', [status(thm)], ['1', '2'])).
% 20.45/20.66  thf(t48_xboole_1, axiom,
% 20.45/20.66    (![A:$i,B:$i]:
% 20.45/20.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 20.45/20.66  thf('4', plain,
% 20.45/20.66      (![X22 : $i, X23 : $i]:
% 20.45/20.66         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 20.45/20.66           = (k3_xboole_0 @ X22 @ X23))),
% 20.45/20.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 20.45/20.66  thf('5', plain,
% 20.45/20.66      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.66         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 20.45/20.66         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 20.45/20.66      inference('sup+', [status(thm)], ['3', '4'])).
% 20.45/20.66  thf(commutativity_k2_tarski, axiom,
% 20.45/20.66    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 20.45/20.66  thf('6', plain,
% 20.45/20.66      (![X26 : $i, X27 : $i]:
% 20.45/20.66         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 20.45/20.66      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 20.45/20.66  thf(t12_setfam_1, axiom,
% 20.45/20.66    (![A:$i,B:$i]:
% 20.45/20.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 20.45/20.66  thf('7', plain,
% 20.45/20.66      (![X46 : $i, X47 : $i]:
% 20.45/20.66         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 20.45/20.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 20.45/20.66  thf('8', plain,
% 20.45/20.66      (![X0 : $i, X1 : $i]:
% 20.45/20.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 20.45/20.66      inference('sup+', [status(thm)], ['6', '7'])).
% 20.45/20.66  thf('9', plain,
% 20.45/20.66      (![X46 : $i, X47 : $i]:
% 20.45/20.66         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 20.45/20.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 20.45/20.66  thf('10', plain,
% 20.45/20.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.45/20.66      inference('sup+', [status(thm)], ['8', '9'])).
% 20.45/20.66  thf(t7_xboole_1, axiom,
% 20.45/20.66    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 20.45/20.66  thf('11', plain,
% 20.45/20.66      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 20.45/20.66      inference('cnf', [status(esa)], [t7_xboole_1])).
% 20.45/20.66  thf('12', plain,
% 20.45/20.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.66  thf(t3_subset, axiom,
% 20.45/20.66    (![A:$i,B:$i]:
% 20.45/20.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 20.45/20.66  thf('13', plain,
% 20.45/20.66      (![X48 : $i, X49 : $i]:
% 20.45/20.66         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 20.45/20.66      inference('cnf', [status(esa)], [t3_subset])).
% 20.45/20.66  thf('14', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 20.45/20.66      inference('sup-', [status(thm)], ['12', '13'])).
% 20.45/20.66  thf(t1_xboole_1, axiom,
% 20.45/20.66    (![A:$i,B:$i,C:$i]:
% 20.45/20.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 20.45/20.66       ( r1_tarski @ A @ C ) ))).
% 20.45/20.66  thf('15', plain,
% 20.45/20.66      (![X7 : $i, X8 : $i, X9 : $i]:
% 20.45/20.66         (~ (r1_tarski @ X7 @ X8)
% 20.45/20.66          | ~ (r1_tarski @ X8 @ X9)
% 20.45/20.66          | (r1_tarski @ X7 @ X9))),
% 20.45/20.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 20.45/20.66  thf('16', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 20.45/20.66      inference('sup-', [status(thm)], ['14', '15'])).
% 20.45/20.66  thf('17', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 20.45/20.66      inference('sup-', [status(thm)], ['11', '16'])).
% 20.45/20.66  thf(t43_xboole_1, axiom,
% 20.45/20.66    (![A:$i,B:$i,C:$i]:
% 20.45/20.66     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 20.45/20.66       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 20.45/20.66  thf('18', plain,
% 20.45/20.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 20.45/20.66         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 20.45/20.66          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 20.45/20.66      inference('cnf', [status(esa)], [t43_xboole_1])).
% 20.45/20.66  thf('19', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 20.45/20.66      inference('sup-', [status(thm)], ['17', '18'])).
% 20.45/20.66  thf(t38_xboole_1, axiom,
% 20.45/20.66    (![A:$i,B:$i]:
% 20.45/20.66     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 20.45/20.66       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 20.45/20.66  thf('20', plain,
% 20.45/20.66      (![X13 : $i, X14 : $i]:
% 20.45/20.66         (((X13) = (k1_xboole_0))
% 20.45/20.66          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 20.45/20.66      inference('cnf', [status(esa)], [t38_xboole_1])).
% 20.45/20.66  thf('21', plain,
% 20.45/20.66      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 20.45/20.66      inference('sup-', [status(thm)], ['19', '20'])).
% 20.45/20.66  thf('22', plain,
% 20.45/20.66      (![X22 : $i, X23 : $i]:
% 20.45/20.66         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 20.45/20.66           = (k3_xboole_0 @ X22 @ X23))),
% 20.45/20.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 20.45/20.66  thf('23', plain,
% 20.45/20.66      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 20.45/20.66         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.45/20.66      inference('sup+', [status(thm)], ['21', '22'])).
% 20.45/20.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 20.45/20.66  thf('24', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 20.45/20.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 20.45/20.66  thf('25', plain,
% 20.45/20.66      (![X48 : $i, X50 : $i]:
% 20.45/20.66         ((m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X48 @ X50))),
% 20.45/20.66      inference('cnf', [status(esa)], [t3_subset])).
% 20.45/20.66  thf('26', plain,
% 20.45/20.66      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 20.45/20.66      inference('sup-', [status(thm)], ['24', '25'])).
% 20.45/20.66  thf('27', plain,
% 20.45/20.66      (![X30 : $i, X31 : $i]:
% 20.45/20.66         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 20.45/20.66          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 20.45/20.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 20.45/20.66  thf('28', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 20.45/20.66      inference('sup-', [status(thm)], ['26', '27'])).
% 20.45/20.66  thf('29', plain,
% 20.45/20.66      (((k3_subset_1 @ sk_B @ k1_xboole_0)
% 20.45/20.66         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.45/20.66      inference('demod', [status(thm)], ['23', '28'])).
% 20.45/20.66  thf('30', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 20.45/20.66      inference('sup-', [status(thm)], ['26', '27'])).
% 20.45/20.66  thf(t3_boole, axiom,
% 20.45/20.66    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 20.45/20.66  thf('31', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 20.45/20.66      inference('cnf', [status(esa)], [t3_boole])).
% 20.45/20.66  thf('32', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 20.45/20.66      inference('sup+', [status(thm)], ['30', '31'])).
% 20.45/20.66  thf('33', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.45/20.66      inference('demod', [status(thm)], ['29', '32'])).
% 20.45/20.66  thf('34', plain,
% 20.45/20.66      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.66         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 20.45/20.66      inference('demod', [status(thm)], ['5', '10', '33'])).
% 20.45/20.66  thf('35', plain,
% 20.45/20.66      (![X22 : $i, X23 : $i]:
% 20.45/20.66         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 20.45/20.66           = (k3_xboole_0 @ X22 @ X23))),
% 20.45/20.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 20.45/20.66  thf(t36_xboole_1, axiom,
% 20.45/20.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 20.45/20.66  thf('36', plain,
% 20.45/20.66      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 20.45/20.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 20.45/20.66  thf(t44_xboole_1, axiom,
% 20.45/20.66    (![A:$i,B:$i,C:$i]:
% 20.45/20.66     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 20.45/20.66       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 20.45/20.66  thf('37', plain,
% 20.45/20.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 20.45/20.66         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 20.45/20.66          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 20.45/20.66      inference('cnf', [status(esa)], [t44_xboole_1])).
% 20.45/20.66  thf('38', plain,
% 20.45/20.66      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 20.45/20.66      inference('sup-', [status(thm)], ['36', '37'])).
% 20.45/20.66  thf('39', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 20.45/20.66      inference('sup-', [status(thm)], ['14', '15'])).
% 20.45/20.66  thf('40', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.66      inference('sup-', [status(thm)], ['38', '39'])).
% 20.45/20.66  thf('41', plain,
% 20.45/20.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 20.45/20.66         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 20.45/20.66          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 20.45/20.66      inference('cnf', [status(esa)], [t43_xboole_1])).
% 20.45/20.66  thf('42', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 20.45/20.66      inference('sup-', [status(thm)], ['40', '41'])).
% 20.45/20.66  thf('43', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 20.45/20.66      inference('sup+', [status(thm)], ['35', '42'])).
% 20.45/20.66  thf('44', plain,
% 20.45/20.66      (![X48 : $i, X50 : $i]:
% 20.45/20.66         ((m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X48 @ X50))),
% 20.45/20.66      inference('cnf', [status(esa)], [t3_subset])).
% 20.45/20.66  thf('45', plain,
% 20.45/20.66      (![X0 : $i]:
% 20.45/20.66         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 20.45/20.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.66      inference('sup-', [status(thm)], ['43', '44'])).
% 20.45/20.66  thf('46', plain,
% 20.45/20.66      (![X30 : $i, X31 : $i]:
% 20.45/20.66         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 20.45/20.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 20.45/20.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 20.45/20.67  thf('47', plain,
% 20.45/20.67      (![X0 : $i]:
% 20.45/20.67         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))
% 20.45/20.67           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['45', '46'])).
% 20.45/20.67  thf('48', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['8', '9'])).
% 20.45/20.67  thf(t17_xboole_1, axiom,
% 20.45/20.67    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 20.45/20.67  thf('49', plain,
% 20.45/20.67      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 20.45/20.67      inference('cnf', [status(esa)], [t17_xboole_1])).
% 20.45/20.67  thf('50', plain,
% 20.45/20.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 20.45/20.67         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 20.45/20.67          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t43_xboole_1])).
% 20.45/20.67  thf('51', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.45/20.67         (r1_tarski @ 
% 20.45/20.67          (k4_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 20.45/20.67          X0)),
% 20.45/20.67      inference('sup-', [status(thm)], ['49', '50'])).
% 20.45/20.67  thf('52', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 20.45/20.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 20.45/20.67  thf(d10_xboole_0, axiom,
% 20.45/20.67    (![A:$i,B:$i]:
% 20.45/20.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 20.45/20.67  thf('53', plain,
% 20.45/20.67      (![X0 : $i, X2 : $i]:
% 20.45/20.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 20.45/20.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.45/20.67  thf('54', plain,
% 20.45/20.67      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['52', '53'])).
% 20.45/20.67  thf('55', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ 
% 20.45/20.67           (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X1) @ X0)
% 20.45/20.67           = (k1_xboole_0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['51', '54'])).
% 20.45/20.67  thf('56', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 20.45/20.67      inference('cnf', [status(esa)], [t3_boole])).
% 20.45/20.67  thf('57', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 20.45/20.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.45/20.67  thf('58', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 20.45/20.67      inference('simplify', [status(thm)], ['57'])).
% 20.45/20.67  thf('59', plain,
% 20.45/20.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 20.45/20.67         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 20.45/20.67          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t43_xboole_1])).
% 20.45/20.67  thf('60', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 20.45/20.67      inference('sup-', [status(thm)], ['58', '59'])).
% 20.45/20.67  thf('61', plain,
% 20.45/20.67      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 20.45/20.67      inference('sup+', [status(thm)], ['56', '60'])).
% 20.45/20.67  thf('62', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['36', '37'])).
% 20.45/20.67  thf('63', plain,
% 20.45/20.67      (![X0 : $i, X2 : $i]:
% 20.45/20.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 20.45/20.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.45/20.67  thf('64', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 20.45/20.67          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['62', '63'])).
% 20.45/20.67  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['61', '64'])).
% 20.45/20.67  thf('66', plain,
% 20.45/20.67      (![X26 : $i, X27 : $i]:
% 20.45/20.67         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 20.45/20.67      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 20.45/20.67  thf(l51_zfmisc_1, axiom,
% 20.45/20.67    (![A:$i,B:$i]:
% 20.45/20.67     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 20.45/20.67  thf('67', plain,
% 20.45/20.67      (![X28 : $i, X29 : $i]:
% 20.45/20.67         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 20.45/20.67      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 20.45/20.67  thf('68', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['66', '67'])).
% 20.45/20.67  thf('69', plain,
% 20.45/20.67      (![X28 : $i, X29 : $i]:
% 20.45/20.67         ((k3_tarski @ (k2_tarski @ X28 @ X29)) = (k2_xboole_0 @ X28 @ X29))),
% 20.45/20.67      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 20.45/20.67  thf('70', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['68', '69'])).
% 20.45/20.67  thf('71', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 20.45/20.67      inference('sup+', [status(thm)], ['65', '70'])).
% 20.45/20.67  thf('72', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 20.45/20.67      inference('demod', [status(thm)], ['55', '71'])).
% 20.45/20.67  thf('73', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 20.45/20.67      inference('sup+', [status(thm)], ['48', '72'])).
% 20.45/20.67  thf('74', plain,
% 20.45/20.67      (![X22 : $i, X23 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 20.45/20.67           = (k3_xboole_0 @ X22 @ X23))),
% 20.45/20.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 20.45/20.67  thf('75', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 20.45/20.67           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 20.45/20.67      inference('sup+', [status(thm)], ['73', '74'])).
% 20.45/20.67  thf('76', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 20.45/20.67      inference('cnf', [status(esa)], [t3_boole])).
% 20.45/20.67  thf('77', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['8', '9'])).
% 20.45/20.67  thf('78', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k3_xboole_0 @ X1 @ X0)
% 20.45/20.67           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.45/20.67      inference('demod', [status(thm)], ['75', '76', '77'])).
% 20.45/20.67  thf(t100_xboole_1, axiom,
% 20.45/20.67    (![A:$i,B:$i]:
% 20.45/20.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 20.45/20.67  thf('79', plain,
% 20.45/20.67      (![X3 : $i, X4 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X3 @ X4)
% 20.45/20.67           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.45/20.67  thf('80', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 20.45/20.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.45/20.67      inference('sup+', [status(thm)], ['78', '79'])).
% 20.45/20.67  thf('81', plain,
% 20.45/20.67      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.67         (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 20.45/20.67         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.67            (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 20.45/20.67      inference('sup+', [status(thm)], ['47', '80'])).
% 20.45/20.67  thf('82', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.45/20.67      inference('demod', [status(thm)], ['29', '32'])).
% 20.45/20.67  thf('83', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 20.45/20.67      inference('demod', [status(thm)], ['29', '32'])).
% 20.45/20.67  thf('84', plain,
% 20.45/20.67      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 20.45/20.67         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 20.45/20.67      inference('demod', [status(thm)], ['81', '82', '83'])).
% 20.45/20.67  thf('85', plain,
% 20.45/20.67      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.67         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 20.45/20.67      inference('demod', [status(thm)], ['34', '84'])).
% 20.45/20.67  thf('86', plain,
% 20.45/20.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.67  thf(dt_k2_tops_1, axiom,
% 20.45/20.67    (![A:$i,B:$i]:
% 20.45/20.67     ( ( ( l1_pre_topc @ A ) & 
% 20.45/20.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 20.45/20.67       ( m1_subset_1 @
% 20.45/20.67         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 20.45/20.67  thf('87', plain,
% 20.45/20.67      (![X51 : $i, X52 : $i]:
% 20.45/20.67         (~ (l1_pre_topc @ X51)
% 20.45/20.67          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 20.45/20.67          | (m1_subset_1 @ (k2_tops_1 @ X51 @ X52) @ 
% 20.45/20.67             (k1_zfmisc_1 @ (u1_struct_0 @ X51))))),
% 20.45/20.67      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 20.45/20.67  thf('88', plain,
% 20.45/20.67      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 20.45/20.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.45/20.67        | ~ (l1_pre_topc @ sk_A))),
% 20.45/20.67      inference('sup-', [status(thm)], ['86', '87'])).
% 20.45/20.67  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 20.45/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.67  thf('90', plain,
% 20.45/20.67      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 20.45/20.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.67      inference('demod', [status(thm)], ['88', '89'])).
% 20.45/20.67  thf('91', plain,
% 20.45/20.67      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 20.45/20.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 20.45/20.67  thf('92', plain,
% 20.45/20.67      (![X48 : $i, X50 : $i]:
% 20.45/20.67         ((m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X48 @ X50))),
% 20.45/20.67      inference('cnf', [status(esa)], [t3_subset])).
% 20.45/20.67  thf('93', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['91', '92'])).
% 20.45/20.67  thf(redefinition_k4_subset_1, axiom,
% 20.45/20.67    (![A:$i,B:$i,C:$i]:
% 20.45/20.67     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 20.45/20.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 20.45/20.67       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 20.45/20.67  thf('94', plain,
% 20.45/20.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 20.45/20.67         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 20.45/20.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 20.45/20.67          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 20.45/20.67      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 20.45/20.67  thf('95', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.45/20.67         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 20.45/20.67            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 20.45/20.67          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['93', '94'])).
% 20.45/20.67  thf('96', plain,
% 20.45/20.67      (![X0 : $i]:
% 20.45/20.67         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.67           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 20.45/20.67           (k2_tops_1 @ sk_A @ sk_B))
% 20.45/20.67           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 20.45/20.67              (k2_tops_1 @ sk_A @ sk_B)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['90', '95'])).
% 20.45/20.67  thf('97', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['68', '69'])).
% 20.45/20.67  thf('98', plain,
% 20.45/20.67      (![X0 : $i]:
% 20.45/20.67         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.67           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 20.45/20.67           (k2_tops_1 @ sk_A @ sk_B))
% 20.45/20.67           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 20.45/20.67              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 20.45/20.67      inference('demod', [status(thm)], ['96', '97'])).
% 20.45/20.67  thf('99', plain,
% 20.45/20.67      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 20.45/20.67         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 20.45/20.67            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.67             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 20.45/20.67      inference('sup+', [status(thm)], ['85', '98'])).
% 20.45/20.67  thf('100', plain,
% 20.45/20.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.67  thf(t65_tops_1, axiom,
% 20.45/20.67    (![A:$i]:
% 20.45/20.67     ( ( l1_pre_topc @ A ) =>
% 20.45/20.67       ( ![B:$i]:
% 20.45/20.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.45/20.67           ( ( k2_pre_topc @ A @ B ) =
% 20.45/20.67             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 20.45/20.67  thf('101', plain,
% 20.45/20.67      (![X58 : $i, X59 : $i]:
% 20.45/20.67         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 20.45/20.67          | ((k2_pre_topc @ X59 @ X58)
% 20.45/20.67              = (k4_subset_1 @ (u1_struct_0 @ X59) @ X58 @ 
% 20.45/20.67                 (k2_tops_1 @ X59 @ X58)))
% 20.45/20.67          | ~ (l1_pre_topc @ X59))),
% 20.45/20.67      inference('cnf', [status(esa)], [t65_tops_1])).
% 20.45/20.67  thf('102', plain,
% 20.45/20.67      ((~ (l1_pre_topc @ sk_A)
% 20.45/20.67        | ((k2_pre_topc @ sk_A @ sk_B)
% 20.45/20.67            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 20.45/20.67               (k2_tops_1 @ sk_A @ sk_B))))),
% 20.45/20.67      inference('sup-', [status(thm)], ['100', '101'])).
% 20.45/20.67  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 20.45/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.67  thf('104', plain,
% 20.45/20.67      (((k2_pre_topc @ sk_A @ sk_B)
% 20.45/20.67         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 20.45/20.67            (k2_tops_1 @ sk_A @ sk_B)))),
% 20.45/20.67      inference('demod', [status(thm)], ['102', '103'])).
% 20.45/20.67  thf('105', plain,
% 20.45/20.67      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 20.45/20.67         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 20.45/20.67      inference('demod', [status(thm)], ['34', '84'])).
% 20.45/20.67  thf('106', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['68', '69'])).
% 20.45/20.67  thf('107', plain,
% 20.45/20.67      (((k2_pre_topc @ sk_A @ sk_B)
% 20.45/20.67         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 20.45/20.67      inference('demod', [status(thm)], ['99', '104', '105', '106'])).
% 20.45/20.67  thf('108', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['68', '69'])).
% 20.45/20.67  thf('109', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['68', '69'])).
% 20.45/20.67  thf('110', plain,
% 20.45/20.67      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 20.45/20.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 20.45/20.67  thf('111', plain,
% 20.45/20.67      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 20.45/20.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 20.45/20.67  thf('112', plain,
% 20.45/20.67      (![X7 : $i, X8 : $i, X9 : $i]:
% 20.45/20.67         (~ (r1_tarski @ X7 @ X8)
% 20.45/20.67          | ~ (r1_tarski @ X8 @ X9)
% 20.45/20.67          | (r1_tarski @ X7 @ X9))),
% 20.45/20.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 20.45/20.67  thf('113', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.45/20.67         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 20.45/20.67      inference('sup-', [status(thm)], ['111', '112'])).
% 20.45/20.67  thf('114', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.45/20.67         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['110', '113'])).
% 20.45/20.67  thf('115', plain,
% 20.45/20.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 20.45/20.67         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 20.45/20.67          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t43_xboole_1])).
% 20.45/20.67  thf('116', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.45/20.67         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X1)) @ X0)),
% 20.45/20.67      inference('sup-', [status(thm)], ['114', '115'])).
% 20.45/20.67  thf('117', plain,
% 20.45/20.67      (![X13 : $i, X14 : $i]:
% 20.45/20.67         (((X13) = (k1_xboole_0))
% 20.45/20.67          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t38_xboole_1])).
% 20.45/20.67  thf('118', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['116', '117'])).
% 20.45/20.67  thf('119', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 20.45/20.67      inference('sup+', [status(thm)], ['109', '118'])).
% 20.45/20.67  thf('120', plain,
% 20.45/20.67      (![X22 : $i, X23 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 20.45/20.67           = (k3_xboole_0 @ X22 @ X23))),
% 20.45/20.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 20.45/20.67  thf('121', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 20.45/20.67           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 20.45/20.67      inference('sup+', [status(thm)], ['119', '120'])).
% 20.45/20.67  thf('122', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 20.45/20.67      inference('cnf', [status(esa)], [t3_boole])).
% 20.45/20.67  thf('123', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 20.45/20.67      inference('demod', [status(thm)], ['121', '122'])).
% 20.45/20.67  thf('124', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['8', '9'])).
% 20.45/20.67  thf('125', plain,
% 20.45/20.67      (![X3 : $i, X4 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X3 @ X4)
% 20.45/20.67           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.45/20.67  thf('126', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X0 @ X1)
% 20.45/20.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.45/20.67      inference('sup+', [status(thm)], ['124', '125'])).
% 20.45/20.67  thf('127', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k3_xboole_0 @ X1 @ X0)
% 20.45/20.67           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.45/20.67      inference('demod', [status(thm)], ['75', '76', '77'])).
% 20.45/20.67  thf('128', plain,
% 20.45/20.67      (![X3 : $i, X4 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X3 @ X4)
% 20.45/20.67           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 20.45/20.67  thf('129', plain,
% 20.45/20.67      (![X22 : $i, X23 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 20.45/20.67           = (k3_xboole_0 @ X22 @ X23))),
% 20.45/20.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 20.45/20.67  thf('130', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 20.45/20.67           = (k3_xboole_0 @ X1 @ X0))),
% 20.45/20.67      inference('sup+', [status(thm)], ['128', '129'])).
% 20.45/20.67  thf('131', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 20.45/20.67           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.45/20.67      inference('sup+', [status(thm)], ['127', '130'])).
% 20.45/20.67  thf('132', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k3_xboole_0 @ X1 @ X0)
% 20.45/20.67           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 20.45/20.67      inference('demod', [status(thm)], ['75', '76', '77'])).
% 20.45/20.67  thf('133', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 20.45/20.67           = (k3_xboole_0 @ X1 @ X0))),
% 20.45/20.67      inference('demod', [status(thm)], ['131', '132'])).
% 20.45/20.67  thf('134', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 20.45/20.67           = (k3_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['126', '133'])).
% 20.45/20.67  thf('135', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['91', '92'])).
% 20.45/20.67  thf('136', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 20.45/20.67      inference('simplify', [status(thm)], ['57'])).
% 20.45/20.67  thf('137', plain,
% 20.45/20.67      (![X48 : $i, X50 : $i]:
% 20.45/20.67         ((m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X48 @ X50))),
% 20.45/20.67      inference('cnf', [status(esa)], [t3_subset])).
% 20.45/20.67  thf('138', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['136', '137'])).
% 20.45/20.67  thf(dt_k4_subset_1, axiom,
% 20.45/20.67    (![A:$i,B:$i,C:$i]:
% 20.45/20.67     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 20.45/20.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 20.45/20.67       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 20.45/20.67  thf('139', plain,
% 20.45/20.67      (![X34 : $i, X35 : $i, X36 : $i]:
% 20.45/20.67         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 20.45/20.67          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 20.45/20.67          | (m1_subset_1 @ (k4_subset_1 @ X35 @ X34 @ X36) @ 
% 20.45/20.67             (k1_zfmisc_1 @ X35)))),
% 20.45/20.67      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 20.45/20.67  thf('140', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 20.45/20.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['138', '139'])).
% 20.45/20.67  thf('141', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 20.45/20.67          (k1_zfmisc_1 @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['135', '140'])).
% 20.45/20.67  thf('142', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['91', '92'])).
% 20.45/20.67  thf('143', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['136', '137'])).
% 20.45/20.67  thf('144', plain,
% 20.45/20.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 20.45/20.67         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 20.45/20.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 20.45/20.67          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 20.45/20.67      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 20.45/20.67  thf('145', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 20.45/20.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['143', '144'])).
% 20.45/20.67  thf('146', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k4_subset_1 @ X0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 20.45/20.67           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['142', '145'])).
% 20.45/20.67  thf('147', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (m1_subset_1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 20.45/20.67          (k1_zfmisc_1 @ X0))),
% 20.45/20.67      inference('demod', [status(thm)], ['141', '146'])).
% 20.45/20.67  thf('148', plain,
% 20.45/20.67      (![X48 : $i, X49 : $i]:
% 20.45/20.67         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t3_subset])).
% 20.45/20.67  thf('149', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X0)),
% 20.45/20.67      inference('sup-', [status(thm)], ['147', '148'])).
% 20.45/20.67  thf('150', plain,
% 20.45/20.67      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 20.45/20.67      inference('cnf', [status(esa)], [t7_xboole_1])).
% 20.45/20.67  thf('151', plain,
% 20.45/20.67      (![X0 : $i, X2 : $i]:
% 20.45/20.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 20.45/20.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.45/20.67  thf('152', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 20.45/20.67          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['150', '151'])).
% 20.45/20.67  thf('153', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['149', '152'])).
% 20.45/20.67  thf('154', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 20.45/20.67      inference('sup+', [status(thm)], ['134', '153'])).
% 20.45/20.67  thf('155', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 20.45/20.67           = (k2_xboole_0 @ X1 @ X0))),
% 20.45/20.67      inference('sup+', [status(thm)], ['123', '154'])).
% 20.45/20.67  thf('156', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['68', '69'])).
% 20.45/20.67  thf('157', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 20.45/20.67           = (k2_xboole_0 @ X1 @ X0))),
% 20.45/20.67      inference('demod', [status(thm)], ['155', '156'])).
% 20.45/20.67  thf('158', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 20.45/20.67           = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['108', '157'])).
% 20.45/20.67  thf('159', plain,
% 20.45/20.67      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 20.45/20.67         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 20.45/20.67      inference('sup+', [status(thm)], ['107', '158'])).
% 20.45/20.67  thf('160', plain,
% 20.45/20.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.67  thf('161', plain,
% 20.45/20.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.45/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.67  thf(t31_tops_1, axiom,
% 20.45/20.67    (![A:$i]:
% 20.45/20.67     ( ( l1_pre_topc @ A ) =>
% 20.45/20.67       ( ![B:$i]:
% 20.45/20.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.45/20.67           ( ![C:$i]:
% 20.45/20.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.45/20.67               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 20.45/20.67                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 20.45/20.67  thf('162', plain,
% 20.45/20.67      (![X53 : $i, X54 : $i, X55 : $i]:
% 20.45/20.67         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 20.45/20.67          | ~ (v4_pre_topc @ X53 @ X54)
% 20.45/20.67          | ~ (r1_tarski @ X55 @ X53)
% 20.45/20.67          | (r1_tarski @ (k2_pre_topc @ X54 @ X55) @ X53)
% 20.45/20.67          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 20.45/20.67          | ~ (l1_pre_topc @ X54))),
% 20.45/20.67      inference('cnf', [status(esa)], [t31_tops_1])).
% 20.45/20.67  thf('163', plain,
% 20.45/20.67      (![X0 : $i]:
% 20.45/20.67         (~ (l1_pre_topc @ sk_A)
% 20.45/20.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.45/20.67          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 20.45/20.67          | ~ (r1_tarski @ X0 @ sk_B)
% 20.45/20.67          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 20.45/20.67      inference('sup-', [status(thm)], ['161', '162'])).
% 20.45/20.67  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 20.45/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.67  thf('165', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 20.45/20.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.45/20.67  thf('166', plain,
% 20.45/20.67      (![X0 : $i]:
% 20.45/20.67         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.45/20.67          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 20.45/20.67          | ~ (r1_tarski @ X0 @ sk_B))),
% 20.45/20.67      inference('demod', [status(thm)], ['163', '164', '165'])).
% 20.45/20.67  thf('167', plain,
% 20.45/20.67      ((~ (r1_tarski @ sk_B @ sk_B)
% 20.45/20.67        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 20.45/20.67      inference('sup-', [status(thm)], ['160', '166'])).
% 20.45/20.67  thf('168', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 20.45/20.67      inference('simplify', [status(thm)], ['57'])).
% 20.45/20.67  thf('169', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 20.45/20.67      inference('demod', [status(thm)], ['167', '168'])).
% 20.45/20.67  thf('170', plain,
% 20.45/20.67      (![X48 : $i, X50 : $i]:
% 20.45/20.67         ((m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X50)) | ~ (r1_tarski @ X48 @ X50))),
% 20.45/20.67      inference('cnf', [status(esa)], [t3_subset])).
% 20.45/20.67  thf('171', plain,
% 20.45/20.67      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 20.45/20.67      inference('sup-', [status(thm)], ['169', '170'])).
% 20.45/20.67  thf('172', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         ((m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 20.45/20.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['138', '139'])).
% 20.45/20.67  thf('173', plain,
% 20.45/20.67      ((m1_subset_1 @ 
% 20.45/20.67        (k4_subset_1 @ sk_B @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.45/20.67        (k1_zfmisc_1 @ sk_B))),
% 20.45/20.67      inference('sup-', [status(thm)], ['171', '172'])).
% 20.45/20.67  thf('174', plain,
% 20.45/20.67      (![X48 : $i, X49 : $i]:
% 20.45/20.67         ((r1_tarski @ X48 @ X49) | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49)))),
% 20.45/20.67      inference('cnf', [status(esa)], [t3_subset])).
% 20.45/20.67  thf('175', plain,
% 20.45/20.67      ((r1_tarski @ 
% 20.45/20.67        (k4_subset_1 @ sk_B @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 20.45/20.67      inference('sup-', [status(thm)], ['173', '174'])).
% 20.45/20.67  thf('176', plain,
% 20.45/20.67      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 20.45/20.67      inference('sup-', [status(thm)], ['169', '170'])).
% 20.45/20.67  thf('177', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 20.45/20.67          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['143', '144'])).
% 20.45/20.67  thf('178', plain,
% 20.45/20.67      (((k4_subset_1 @ sk_B @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 20.45/20.67         = (k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['176', '177'])).
% 20.45/20.67  thf('179', plain,
% 20.45/20.67      ((r1_tarski @ (k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 20.45/20.67      inference('demod', [status(thm)], ['175', '178'])).
% 20.45/20.67  thf('180', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]:
% 20.45/20.67         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 20.45/20.67          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 20.45/20.67      inference('sup-', [status(thm)], ['150', '151'])).
% 20.45/20.67  thf('181', plain,
% 20.45/20.67      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 20.45/20.67      inference('sup-', [status(thm)], ['179', '180'])).
% 20.45/20.67  thf('182', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.45/20.67      inference('sup+', [status(thm)], ['68', '69'])).
% 20.45/20.67  thf('183', plain,
% 20.45/20.67      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 20.45/20.67      inference('demod', [status(thm)], ['159', '181', '182'])).
% 20.45/20.67  thf('184', plain,
% 20.45/20.67      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 20.45/20.67      inference('sup-', [status(thm)], ['36', '37'])).
% 20.45/20.67  thf('185', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 20.45/20.67      inference('sup+', [status(thm)], ['183', '184'])).
% 20.45/20.67  thf('186', plain, ($false), inference('demod', [status(thm)], ['0', '185'])).
% 20.45/20.67  
% 20.45/20.67  % SZS output end Refutation
% 20.45/20.67  
% 20.45/20.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
