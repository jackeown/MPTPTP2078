%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IE3cqYGkuN

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:13 EST 2020

% Result     : Theorem 18.74s
% Output     : Refutation 18.74s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 190 expanded)
%              Number of leaves         :   35 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  736 (1569 expanded)
%              Number of equality atoms :   50 ( 101 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_tarski @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X31 @ X30 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k6_subset_1 @ X26 @ ( k6_subset_1 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('23',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( l1_pre_topc @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X48 @ X49 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X36: $i,X37: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k2_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_pre_topc @ X56 @ X55 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','38','39'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v4_pre_topc @ X50 @ X51 )
      | ~ ( r1_tarski @ X52 @ X50 )
      | ( r1_tarski @ ( k2_pre_topc @ X51 @ X52 ) @ X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['55','56'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IE3cqYGkuN
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 18.74/18.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.74/18.91  % Solved by: fo/fo7.sh
% 18.74/18.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.74/18.91  % done 17182 iterations in 18.443s
% 18.74/18.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.74/18.91  % SZS output start Refutation
% 18.74/18.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.74/18.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 18.74/18.91  thf(sk_A_type, type, sk_A: $i).
% 18.74/18.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 18.74/18.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 18.74/18.91  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 18.74/18.91  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 18.74/18.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 18.74/18.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.74/18.91  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 18.74/18.91  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 18.74/18.91  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 18.74/18.91  thf(sk_B_type, type, sk_B: $i).
% 18.74/18.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 18.74/18.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.74/18.91  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 18.74/18.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 18.74/18.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 18.74/18.91  thf(t69_tops_1, conjecture,
% 18.74/18.91    (![A:$i]:
% 18.74/18.91     ( ( l1_pre_topc @ A ) =>
% 18.74/18.91       ( ![B:$i]:
% 18.74/18.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.74/18.91           ( ( v4_pre_topc @ B @ A ) =>
% 18.74/18.91             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 18.74/18.91  thf(zf_stmt_0, negated_conjecture,
% 18.74/18.91    (~( ![A:$i]:
% 18.74/18.91        ( ( l1_pre_topc @ A ) =>
% 18.74/18.91          ( ![B:$i]:
% 18.74/18.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.74/18.91              ( ( v4_pre_topc @ B @ A ) =>
% 18.74/18.91                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 18.74/18.91    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 18.74/18.91  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf('1', plain,
% 18.74/18.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf(t3_subset, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 18.74/18.91  thf('2', plain,
% 18.74/18.91      (![X45 : $i, X46 : $i]:
% 18.74/18.91         ((r1_tarski @ X45 @ X46) | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46)))),
% 18.74/18.91      inference('cnf', [status(esa)], [t3_subset])).
% 18.74/18.91  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 18.74/18.91      inference('sup-', [status(thm)], ['1', '2'])).
% 18.74/18.91  thf(t28_xboole_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 18.74/18.91  thf('4', plain,
% 18.74/18.91      (![X17 : $i, X18 : $i]:
% 18.74/18.91         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 18.74/18.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 18.74/18.91  thf('5', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 18.74/18.91      inference('sup-', [status(thm)], ['3', '4'])).
% 18.74/18.91  thf(commutativity_k2_tarski, axiom,
% 18.74/18.91    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 18.74/18.91  thf('6', plain,
% 18.74/18.91      (![X30 : $i, X31 : $i]:
% 18.74/18.91         ((k2_tarski @ X31 @ X30) = (k2_tarski @ X30 @ X31))),
% 18.74/18.91      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 18.74/18.91  thf(t12_setfam_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 18.74/18.91  thf('7', plain,
% 18.74/18.91      (![X43 : $i, X44 : $i]:
% 18.74/18.91         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 18.74/18.91      inference('cnf', [status(esa)], [t12_setfam_1])).
% 18.74/18.91  thf('8', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i]:
% 18.74/18.91         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 18.74/18.91      inference('sup+', [status(thm)], ['6', '7'])).
% 18.74/18.91  thf('9', plain,
% 18.74/18.91      (![X43 : $i, X44 : $i]:
% 18.74/18.91         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 18.74/18.91      inference('cnf', [status(esa)], [t12_setfam_1])).
% 18.74/18.91  thf('10', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.74/18.91      inference('sup+', [status(thm)], ['8', '9'])).
% 18.74/18.91  thf(t100_xboole_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 18.74/18.91  thf('11', plain,
% 18.74/18.91      (![X8 : $i, X9 : $i]:
% 18.74/18.91         ((k4_xboole_0 @ X8 @ X9)
% 18.74/18.91           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 18.74/18.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.74/18.91  thf(redefinition_k6_subset_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 18.74/18.91  thf('12', plain,
% 18.74/18.91      (![X41 : $i, X42 : $i]:
% 18.74/18.91         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 18.74/18.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.74/18.91  thf('13', plain,
% 18.74/18.91      (![X8 : $i, X9 : $i]:
% 18.74/18.91         ((k6_subset_1 @ X8 @ X9)
% 18.74/18.91           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 18.74/18.91      inference('demod', [status(thm)], ['11', '12'])).
% 18.74/18.91  thf('14', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i]:
% 18.74/18.91         ((k6_subset_1 @ X0 @ X1)
% 18.74/18.91           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 18.74/18.91      inference('sup+', [status(thm)], ['10', '13'])).
% 18.74/18.91  thf('15', plain,
% 18.74/18.91      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 18.74/18.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 18.74/18.91      inference('sup+', [status(thm)], ['5', '14'])).
% 18.74/18.91  thf(t48_xboole_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 18.74/18.91  thf('16', plain,
% 18.74/18.91      (![X26 : $i, X27 : $i]:
% 18.74/18.91         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 18.74/18.91           = (k3_xboole_0 @ X26 @ X27))),
% 18.74/18.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 18.74/18.91  thf('17', plain,
% 18.74/18.91      (![X41 : $i, X42 : $i]:
% 18.74/18.91         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 18.74/18.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.74/18.91  thf('18', plain,
% 18.74/18.91      (![X41 : $i, X42 : $i]:
% 18.74/18.91         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 18.74/18.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.74/18.91  thf('19', plain,
% 18.74/18.91      (![X26 : $i, X27 : $i]:
% 18.74/18.91         ((k6_subset_1 @ X26 @ (k6_subset_1 @ X26 @ X27))
% 18.74/18.91           = (k3_xboole_0 @ X26 @ X27))),
% 18.74/18.91      inference('demod', [status(thm)], ['16', '17', '18'])).
% 18.74/18.91  thf('20', plain,
% 18.74/18.91      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 18.74/18.91         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 18.74/18.91         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 18.74/18.91      inference('sup+', [status(thm)], ['15', '19'])).
% 18.74/18.91  thf('21', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 18.74/18.91      inference('sup+', [status(thm)], ['8', '9'])).
% 18.74/18.91  thf('22', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 18.74/18.91      inference('sup-', [status(thm)], ['3', '4'])).
% 18.74/18.91  thf('23', plain,
% 18.74/18.91      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 18.74/18.91         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 18.74/18.91      inference('demod', [status(thm)], ['20', '21', '22'])).
% 18.74/18.91  thf('24', plain,
% 18.74/18.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf(dt_k2_tops_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( ( ( l1_pre_topc @ A ) & 
% 18.74/18.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 18.74/18.91       ( m1_subset_1 @
% 18.74/18.91         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 18.74/18.91  thf('25', plain,
% 18.74/18.91      (![X48 : $i, X49 : $i]:
% 18.74/18.91         (~ (l1_pre_topc @ X48)
% 18.74/18.91          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 18.74/18.91          | (m1_subset_1 @ (k2_tops_1 @ X48 @ X49) @ 
% 18.74/18.91             (k1_zfmisc_1 @ (u1_struct_0 @ X48))))),
% 18.74/18.91      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 18.74/18.91  thf('26', plain,
% 18.74/18.91      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 18.74/18.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 18.74/18.91        | ~ (l1_pre_topc @ sk_A))),
% 18.74/18.91      inference('sup-', [status(thm)], ['24', '25'])).
% 18.74/18.91  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf('28', plain,
% 18.74/18.91      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 18.74/18.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.74/18.91      inference('demod', [status(thm)], ['26', '27'])).
% 18.74/18.91  thf(dt_k6_subset_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 18.74/18.91  thf('29', plain,
% 18.74/18.91      (![X36 : $i, X37 : $i]:
% 18.74/18.91         (m1_subset_1 @ (k6_subset_1 @ X36 @ X37) @ (k1_zfmisc_1 @ X36))),
% 18.74/18.91      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 18.74/18.91  thf(redefinition_k4_subset_1, axiom,
% 18.74/18.91    (![A:$i,B:$i,C:$i]:
% 18.74/18.91     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 18.74/18.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 18.74/18.91       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 18.74/18.91  thf('30', plain,
% 18.74/18.91      (![X38 : $i, X39 : $i, X40 : $i]:
% 18.74/18.91         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 18.74/18.91          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 18.74/18.91          | ((k4_subset_1 @ X39 @ X38 @ X40) = (k2_xboole_0 @ X38 @ X40)))),
% 18.74/18.91      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 18.74/18.91  thf('31', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.74/18.91         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 18.74/18.91            = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2))
% 18.74/18.91          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 18.74/18.91      inference('sup-', [status(thm)], ['29', '30'])).
% 18.74/18.91  thf('32', plain,
% 18.74/18.91      (![X0 : $i]:
% 18.74/18.91         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 18.74/18.91           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 18.74/18.91           (k2_tops_1 @ sk_A @ sk_B))
% 18.74/18.91           = (k2_xboole_0 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 18.74/18.91              (k2_tops_1 @ sk_A @ sk_B)))),
% 18.74/18.91      inference('sup-', [status(thm)], ['28', '31'])).
% 18.74/18.91  thf('33', plain,
% 18.74/18.91      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 18.74/18.91         = (k2_xboole_0 @ 
% 18.74/18.91            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 18.74/18.91             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 18.74/18.91            (k2_tops_1 @ sk_A @ sk_B)))),
% 18.74/18.91      inference('sup+', [status(thm)], ['23', '32'])).
% 18.74/18.91  thf('34', plain,
% 18.74/18.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf(t65_tops_1, axiom,
% 18.74/18.91    (![A:$i]:
% 18.74/18.91     ( ( l1_pre_topc @ A ) =>
% 18.74/18.91       ( ![B:$i]:
% 18.74/18.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.74/18.91           ( ( k2_pre_topc @ A @ B ) =
% 18.74/18.91             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 18.74/18.91  thf('35', plain,
% 18.74/18.91      (![X55 : $i, X56 : $i]:
% 18.74/18.91         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 18.74/18.91          | ((k2_pre_topc @ X56 @ X55)
% 18.74/18.91              = (k4_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 18.74/18.91                 (k2_tops_1 @ X56 @ X55)))
% 18.74/18.91          | ~ (l1_pre_topc @ X56))),
% 18.74/18.91      inference('cnf', [status(esa)], [t65_tops_1])).
% 18.74/18.91  thf('36', plain,
% 18.74/18.91      ((~ (l1_pre_topc @ sk_A)
% 18.74/18.91        | ((k2_pre_topc @ sk_A @ sk_B)
% 18.74/18.91            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 18.74/18.91               (k2_tops_1 @ sk_A @ sk_B))))),
% 18.74/18.91      inference('sup-', [status(thm)], ['34', '35'])).
% 18.74/18.91  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf('38', plain,
% 18.74/18.91      (((k2_pre_topc @ sk_A @ sk_B)
% 18.74/18.91         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 18.74/18.91            (k2_tops_1 @ sk_A @ sk_B)))),
% 18.74/18.91      inference('demod', [status(thm)], ['36', '37'])).
% 18.74/18.91  thf('39', plain,
% 18.74/18.91      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 18.74/18.91         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 18.74/18.91      inference('demod', [status(thm)], ['20', '21', '22'])).
% 18.74/18.91  thf('40', plain,
% 18.74/18.91      (((k2_pre_topc @ sk_A @ sk_B)
% 18.74/18.91         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 18.74/18.91      inference('demod', [status(thm)], ['33', '38', '39'])).
% 18.74/18.91  thf(t7_xboole_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 18.74/18.91  thf('41', plain,
% 18.74/18.91      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 18.74/18.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 18.74/18.91  thf(t12_xboole_1, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 18.74/18.91  thf('42', plain,
% 18.74/18.91      (![X10 : $i, X11 : $i]:
% 18.74/18.91         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 18.74/18.91      inference('cnf', [status(esa)], [t12_xboole_1])).
% 18.74/18.91  thf('43', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i]:
% 18.74/18.91         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 18.74/18.91           = (k2_xboole_0 @ X1 @ X0))),
% 18.74/18.91      inference('sup-', [status(thm)], ['41', '42'])).
% 18.74/18.91  thf('44', plain,
% 18.74/18.91      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 18.74/18.91         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 18.74/18.91      inference('sup+', [status(thm)], ['40', '43'])).
% 18.74/18.91  thf('45', plain,
% 18.74/18.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf('46', plain,
% 18.74/18.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf(t31_tops_1, axiom,
% 18.74/18.91    (![A:$i]:
% 18.74/18.91     ( ( l1_pre_topc @ A ) =>
% 18.74/18.91       ( ![B:$i]:
% 18.74/18.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.74/18.91           ( ![C:$i]:
% 18.74/18.91             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.74/18.91               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 18.74/18.91                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 18.74/18.91  thf('47', plain,
% 18.74/18.91      (![X50 : $i, X51 : $i, X52 : $i]:
% 18.74/18.91         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 18.74/18.91          | ~ (v4_pre_topc @ X50 @ X51)
% 18.74/18.91          | ~ (r1_tarski @ X52 @ X50)
% 18.74/18.91          | (r1_tarski @ (k2_pre_topc @ X51 @ X52) @ X50)
% 18.74/18.91          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 18.74/18.91          | ~ (l1_pre_topc @ X51))),
% 18.74/18.91      inference('cnf', [status(esa)], [t31_tops_1])).
% 18.74/18.91  thf('48', plain,
% 18.74/18.91      (![X0 : $i]:
% 18.74/18.91         (~ (l1_pre_topc @ sk_A)
% 18.74/18.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 18.74/18.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 18.74/18.91          | ~ (r1_tarski @ X0 @ sk_B)
% 18.74/18.91          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 18.74/18.91      inference('sup-', [status(thm)], ['46', '47'])).
% 18.74/18.91  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf('50', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 18.74/18.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.91  thf('51', plain,
% 18.74/18.91      (![X0 : $i]:
% 18.74/18.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 18.74/18.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 18.74/18.91          | ~ (r1_tarski @ X0 @ sk_B))),
% 18.74/18.91      inference('demod', [status(thm)], ['48', '49', '50'])).
% 18.74/18.91  thf('52', plain,
% 18.74/18.91      ((~ (r1_tarski @ sk_B @ sk_B)
% 18.74/18.91        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 18.74/18.91      inference('sup-', [status(thm)], ['45', '51'])).
% 18.74/18.91  thf(d10_xboole_0, axiom,
% 18.74/18.91    (![A:$i,B:$i]:
% 18.74/18.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 18.74/18.91  thf('53', plain,
% 18.74/18.91      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 18.74/18.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 18.74/18.91  thf('54', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 18.74/18.91      inference('simplify', [status(thm)], ['53'])).
% 18.74/18.91  thf('55', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 18.74/18.91      inference('demod', [status(thm)], ['52', '54'])).
% 18.74/18.91  thf('56', plain,
% 18.74/18.91      (![X10 : $i, X11 : $i]:
% 18.74/18.91         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 18.74/18.91      inference('cnf', [status(esa)], [t12_xboole_1])).
% 18.74/18.91  thf('57', plain,
% 18.74/18.91      (((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 18.74/18.91      inference('sup-', [status(thm)], ['55', '56'])).
% 18.74/18.91  thf(commutativity_k2_xboole_0, axiom,
% 18.74/18.91    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 18.74/18.91  thf('58', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.74/18.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.74/18.91  thf('59', plain,
% 18.74/18.91      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 18.74/18.91      inference('demod', [status(thm)], ['57', '58'])).
% 18.74/18.91  thf('60', plain,
% 18.74/18.91      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 18.74/18.91      inference('demod', [status(thm)], ['44', '59'])).
% 18.74/18.91  thf('61', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 18.74/18.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 18.74/18.91  thf('62', plain,
% 18.74/18.91      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 18.74/18.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 18.74/18.91  thf('63', plain,
% 18.74/18.91      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 18.74/18.91      inference('sup+', [status(thm)], ['61', '62'])).
% 18.74/18.91  thf('64', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 18.74/18.91      inference('sup+', [status(thm)], ['60', '63'])).
% 18.74/18.91  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 18.74/18.91  
% 18.74/18.91  % SZS output end Refutation
% 18.74/18.91  
% 18.74/18.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
