%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wVNS1Aydi6

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:13 EST 2020

% Result     : Theorem 12.51s
% Output     : Refutation 12.51s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 176 expanded)
%              Number of leaves         :   37 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  785 (1379 expanded)
%              Number of equality atoms :   46 (  70 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( l1_pre_topc @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X53 @ X54 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ X0 ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('41',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k2_pre_topc @ X61 @ X60 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X61 ) @ X60 @ ( k2_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('46',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','44','45'])).

thf('47',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v4_pre_topc @ X55 @ X56 )
      | ~ ( r1_tarski @ X57 @ X55 )
      | ( r1_tarski @ ( k2_pre_topc @ X56 @ X57 ) @ X55 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('63',plain,
    ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['61','62'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('64',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_tarski @ X29 @ X28 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('72',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wVNS1Aydi6
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.51/12.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.51/12.72  % Solved by: fo/fo7.sh
% 12.51/12.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.51/12.72  % done 20539 iterations in 12.259s
% 12.51/12.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.51/12.72  % SZS output start Refutation
% 12.51/12.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.51/12.72  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 12.51/12.72  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 12.51/12.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.51/12.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.51/12.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.51/12.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.51/12.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 12.51/12.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.51/12.72  thf(sk_B_type, type, sk_B: $i).
% 12.51/12.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.51/12.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.51/12.72  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 12.51/12.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 12.51/12.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.51/12.72  thf(sk_A_type, type, sk_A: $i).
% 12.51/12.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 12.51/12.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.51/12.72  thf(t69_tops_1, conjecture,
% 12.51/12.72    (![A:$i]:
% 12.51/12.72     ( ( l1_pre_topc @ A ) =>
% 12.51/12.72       ( ![B:$i]:
% 12.51/12.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.51/12.72           ( ( v4_pre_topc @ B @ A ) =>
% 12.51/12.72             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 12.51/12.72  thf(zf_stmt_0, negated_conjecture,
% 12.51/12.72    (~( ![A:$i]:
% 12.51/12.72        ( ( l1_pre_topc @ A ) =>
% 12.51/12.72          ( ![B:$i]:
% 12.51/12.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.51/12.72              ( ( v4_pre_topc @ B @ A ) =>
% 12.51/12.72                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 12.51/12.72    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 12.51/12.72  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf(t7_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 12.51/12.72  thf('1', plain,
% 12.51/12.72      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 12.51/12.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.51/12.72  thf(t43_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i,C:$i]:
% 12.51/12.72     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 12.51/12.72       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 12.51/12.72  thf('2', plain,
% 12.51/12.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.51/12.72         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 12.51/12.72          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 12.51/12.72      inference('cnf', [status(esa)], [t43_xboole_1])).
% 12.51/12.72  thf('3', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 12.51/12.72      inference('sup-', [status(thm)], ['1', '2'])).
% 12.51/12.72  thf(t38_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i]:
% 12.51/12.72     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 12.51/12.72       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 12.51/12.72  thf('4', plain,
% 12.51/12.72      (![X15 : $i, X16 : $i]:
% 12.51/12.72         (((X15) = (k1_xboole_0))
% 12.51/12.72          | ~ (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 12.51/12.72      inference('cnf', [status(esa)], [t38_xboole_1])).
% 12.51/12.72  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.51/12.72      inference('sup-', [status(thm)], ['3', '4'])).
% 12.51/12.72  thf(t48_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i]:
% 12.51/12.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 12.51/12.72  thf('6', plain,
% 12.51/12.72      (![X24 : $i, X25 : $i]:
% 12.51/12.72         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 12.51/12.72           = (k3_xboole_0 @ X24 @ X25))),
% 12.51/12.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 12.51/12.72  thf('7', plain,
% 12.51/12.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 12.51/12.72      inference('sup+', [status(thm)], ['5', '6'])).
% 12.51/12.72  thf(t3_boole, axiom,
% 12.51/12.72    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 12.51/12.72  thf('8', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 12.51/12.72      inference('cnf', [status(esa)], [t3_boole])).
% 12.51/12.72  thf('9', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 12.51/12.72      inference('demod', [status(thm)], ['7', '8'])).
% 12.51/12.72  thf(t100_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i]:
% 12.51/12.72     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 12.51/12.72  thf('10', plain,
% 12.51/12.72      (![X3 : $i, X4 : $i]:
% 12.51/12.72         ((k4_xboole_0 @ X3 @ X4)
% 12.51/12.72           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 12.51/12.72      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.51/12.72  thf('11', plain,
% 12.51/12.72      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 12.51/12.72      inference('sup+', [status(thm)], ['9', '10'])).
% 12.51/12.72  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.51/12.72      inference('sup-', [status(thm)], ['3', '4'])).
% 12.51/12.72  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 12.51/12.72      inference('sup+', [status(thm)], ['11', '12'])).
% 12.51/12.72  thf('14', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 12.51/12.72      inference('cnf', [status(esa)], [t3_boole])).
% 12.51/12.72  thf('15', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]:
% 12.51/12.72         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 12.51/12.72      inference('sup+', [status(thm)], ['13', '14'])).
% 12.51/12.72  thf('16', plain,
% 12.51/12.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf(dt_k2_tops_1, axiom,
% 12.51/12.72    (![A:$i,B:$i]:
% 12.51/12.72     ( ( ( l1_pre_topc @ A ) & 
% 12.51/12.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.51/12.72       ( m1_subset_1 @
% 12.51/12.72         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 12.51/12.72  thf('17', plain,
% 12.51/12.72      (![X53 : $i, X54 : $i]:
% 12.51/12.72         (~ (l1_pre_topc @ X53)
% 12.51/12.72          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 12.51/12.72          | (m1_subset_1 @ (k2_tops_1 @ X53 @ X54) @ 
% 12.51/12.72             (k1_zfmisc_1 @ (u1_struct_0 @ X53))))),
% 12.51/12.72      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 12.51/12.72  thf('18', plain,
% 12.51/12.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 12.51/12.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.51/12.72        | ~ (l1_pre_topc @ sk_A))),
% 12.51/12.72      inference('sup-', [status(thm)], ['16', '17'])).
% 12.51/12.72  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf('20', plain,
% 12.51/12.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 12.51/12.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.51/12.72      inference('demod', [status(thm)], ['18', '19'])).
% 12.51/12.72  thf(t36_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 12.51/12.72  thf('21', plain,
% 12.51/12.72      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 12.51/12.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 12.51/12.72  thf(t44_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i,C:$i]:
% 12.51/12.72     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 12.51/12.72       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 12.51/12.72  thf('22', plain,
% 12.51/12.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.51/12.72         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 12.51/12.72          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 12.51/12.72      inference('cnf', [status(esa)], [t44_xboole_1])).
% 12.51/12.72  thf('23', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 12.51/12.72      inference('sup-', [status(thm)], ['21', '22'])).
% 12.51/12.72  thf('24', plain,
% 12.51/12.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf(t3_subset, axiom,
% 12.51/12.72    (![A:$i,B:$i]:
% 12.51/12.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.51/12.72  thf('25', plain,
% 12.51/12.72      (![X50 : $i, X51 : $i]:
% 12.51/12.72         ((r1_tarski @ X50 @ X51) | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51)))),
% 12.51/12.72      inference('cnf', [status(esa)], [t3_subset])).
% 12.51/12.72  thf('26', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 12.51/12.72      inference('sup-', [status(thm)], ['24', '25'])).
% 12.51/12.72  thf(t12_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i]:
% 12.51/12.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 12.51/12.72  thf('27', plain,
% 12.51/12.72      (![X8 : $i, X9 : $i]:
% 12.51/12.72         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 12.51/12.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.51/12.72  thf('28', plain,
% 12.51/12.72      (((k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 12.51/12.72      inference('sup-', [status(thm)], ['26', '27'])).
% 12.51/12.72  thf(t11_xboole_1, axiom,
% 12.51/12.72    (![A:$i,B:$i,C:$i]:
% 12.51/12.72     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 12.51/12.72  thf('29', plain,
% 12.51/12.72      (![X5 : $i, X6 : $i, X7 : $i]:
% 12.51/12.72         ((r1_tarski @ X5 @ X6) | ~ (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 12.51/12.72      inference('cnf', [status(esa)], [t11_xboole_1])).
% 12.51/12.72  thf('30', plain,
% 12.51/12.72      (![X0 : $i]:
% 12.51/12.72         (~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0) | (r1_tarski @ sk_B @ X0))),
% 12.51/12.72      inference('sup-', [status(thm)], ['28', '29'])).
% 12.51/12.72  thf('31', plain,
% 12.51/12.72      (![X0 : $i]:
% 12.51/12.72         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 12.51/12.72      inference('sup-', [status(thm)], ['23', '30'])).
% 12.51/12.72  thf('32', plain,
% 12.51/12.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 12.51/12.72         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 12.51/12.72          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 12.51/12.72      inference('cnf', [status(esa)], [t43_xboole_1])).
% 12.51/12.72  thf('33', plain,
% 12.51/12.72      (![X0 : $i]:
% 12.51/12.72         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 12.51/12.72      inference('sup-', [status(thm)], ['31', '32'])).
% 12.51/12.72  thf('34', plain,
% 12.51/12.72      (![X50 : $i, X52 : $i]:
% 12.51/12.72         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 12.51/12.72      inference('cnf', [status(esa)], [t3_subset])).
% 12.51/12.72  thf('35', plain,
% 12.51/12.72      (![X0 : $i]:
% 12.51/12.72         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 12.51/12.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.51/12.72      inference('sup-', [status(thm)], ['33', '34'])).
% 12.51/12.72  thf(redefinition_k4_subset_1, axiom,
% 12.51/12.72    (![A:$i,B:$i,C:$i]:
% 12.51/12.72     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 12.51/12.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 12.51/12.72       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 12.51/12.72  thf('36', plain,
% 12.51/12.72      (![X39 : $i, X40 : $i, X41 : $i]:
% 12.51/12.72         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 12.51/12.72          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 12.51/12.72          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 12.51/12.72      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 12.51/12.72  thf('37', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]:
% 12.51/12.72         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 12.51/12.72            = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1))
% 12.51/12.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.51/12.72      inference('sup-', [status(thm)], ['35', '36'])).
% 12.51/12.72  thf('38', plain,
% 12.51/12.72      (![X0 : $i]:
% 12.51/12.72         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0) @ 
% 12.51/12.72           (k2_tops_1 @ sk_A @ sk_B))
% 12.51/12.72           = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 12.51/12.72              (k2_tops_1 @ sk_A @ sk_B)))),
% 12.51/12.72      inference('sup-', [status(thm)], ['20', '37'])).
% 12.51/12.72  thf('39', plain,
% 12.51/12.72      (![X0 : $i]:
% 12.51/12.72         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 12.51/12.72           (k2_tops_1 @ sk_A @ sk_B))
% 12.51/12.72           = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ X0)) @ 
% 12.51/12.72              (k2_tops_1 @ sk_A @ sk_B)))),
% 12.51/12.72      inference('sup+', [status(thm)], ['15', '38'])).
% 12.51/12.72  thf('40', plain,
% 12.51/12.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf(t65_tops_1, axiom,
% 12.51/12.72    (![A:$i]:
% 12.51/12.72     ( ( l1_pre_topc @ A ) =>
% 12.51/12.72       ( ![B:$i]:
% 12.51/12.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.51/12.72           ( ( k2_pre_topc @ A @ B ) =
% 12.51/12.72             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 12.51/12.72  thf('41', plain,
% 12.51/12.72      (![X60 : $i, X61 : $i]:
% 12.51/12.72         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 12.51/12.72          | ((k2_pre_topc @ X61 @ X60)
% 12.51/12.72              = (k4_subset_1 @ (u1_struct_0 @ X61) @ X60 @ 
% 12.51/12.72                 (k2_tops_1 @ X61 @ X60)))
% 12.51/12.72          | ~ (l1_pre_topc @ X61))),
% 12.51/12.72      inference('cnf', [status(esa)], [t65_tops_1])).
% 12.51/12.72  thf('42', plain,
% 12.51/12.72      ((~ (l1_pre_topc @ sk_A)
% 12.51/12.72        | ((k2_pre_topc @ sk_A @ sk_B)
% 12.51/12.72            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 12.51/12.72               (k2_tops_1 @ sk_A @ sk_B))))),
% 12.51/12.72      inference('sup-', [status(thm)], ['40', '41'])).
% 12.51/12.72  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf('44', plain,
% 12.51/12.72      (((k2_pre_topc @ sk_A @ sk_B)
% 12.51/12.72         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 12.51/12.72            (k2_tops_1 @ sk_A @ sk_B)))),
% 12.51/12.72      inference('demod', [status(thm)], ['42', '43'])).
% 12.51/12.72  thf('45', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]:
% 12.51/12.72         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 12.51/12.72      inference('sup+', [status(thm)], ['13', '14'])).
% 12.51/12.72  thf('46', plain,
% 12.51/12.72      (((k2_pre_topc @ sk_A @ sk_B)
% 12.51/12.72         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 12.51/12.72      inference('demod', [status(thm)], ['39', '44', '45'])).
% 12.51/12.72  thf('47', plain,
% 12.51/12.72      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 12.51/12.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.51/12.72  thf('48', plain,
% 12.51/12.72      (![X8 : $i, X9 : $i]:
% 12.51/12.72         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 12.51/12.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.51/12.72  thf('49', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]:
% 12.51/12.72         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 12.51/12.72           = (k2_xboole_0 @ X1 @ X0))),
% 12.51/12.72      inference('sup-', [status(thm)], ['47', '48'])).
% 12.51/12.72  thf('50', plain,
% 12.51/12.72      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 12.51/12.72         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 12.51/12.72      inference('sup+', [status(thm)], ['46', '49'])).
% 12.51/12.72  thf('51', plain,
% 12.51/12.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf('52', plain,
% 12.51/12.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf(t31_tops_1, axiom,
% 12.51/12.72    (![A:$i]:
% 12.51/12.72     ( ( l1_pre_topc @ A ) =>
% 12.51/12.72       ( ![B:$i]:
% 12.51/12.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.51/12.72           ( ![C:$i]:
% 12.51/12.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.51/12.72               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 12.51/12.72                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 12.51/12.72  thf('53', plain,
% 12.51/12.72      (![X55 : $i, X56 : $i, X57 : $i]:
% 12.51/12.72         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 12.51/12.72          | ~ (v4_pre_topc @ X55 @ X56)
% 12.51/12.72          | ~ (r1_tarski @ X57 @ X55)
% 12.51/12.72          | (r1_tarski @ (k2_pre_topc @ X56 @ X57) @ X55)
% 12.51/12.72          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 12.51/12.72          | ~ (l1_pre_topc @ X56))),
% 12.51/12.72      inference('cnf', [status(esa)], [t31_tops_1])).
% 12.51/12.72  thf('54', plain,
% 12.51/12.72      (![X0 : $i]:
% 12.51/12.72         (~ (l1_pre_topc @ sk_A)
% 12.51/12.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.51/12.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 12.51/12.72          | ~ (r1_tarski @ X0 @ sk_B)
% 12.51/12.72          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 12.51/12.72      inference('sup-', [status(thm)], ['52', '53'])).
% 12.51/12.72  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf('56', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 12.51/12.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.51/12.72  thf('57', plain,
% 12.51/12.72      (![X0 : $i]:
% 12.51/12.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.51/12.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 12.51/12.72          | ~ (r1_tarski @ X0 @ sk_B))),
% 12.51/12.72      inference('demod', [status(thm)], ['54', '55', '56'])).
% 12.51/12.72  thf('58', plain,
% 12.51/12.72      ((~ (r1_tarski @ sk_B @ sk_B)
% 12.51/12.72        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 12.51/12.72      inference('sup-', [status(thm)], ['51', '57'])).
% 12.51/12.72  thf(d10_xboole_0, axiom,
% 12.51/12.72    (![A:$i,B:$i]:
% 12.51/12.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.51/12.72  thf('59', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 12.51/12.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.51/12.72  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 12.51/12.72      inference('simplify', [status(thm)], ['59'])).
% 12.51/12.72  thf('61', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 12.51/12.72      inference('demod', [status(thm)], ['58', '60'])).
% 12.51/12.72  thf('62', plain,
% 12.51/12.72      (![X8 : $i, X9 : $i]:
% 12.51/12.72         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 12.51/12.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 12.51/12.72  thf('63', plain,
% 12.51/12.72      (((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 12.51/12.72      inference('sup-', [status(thm)], ['61', '62'])).
% 12.51/12.72  thf(commutativity_k2_tarski, axiom,
% 12.51/12.72    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 12.51/12.72  thf('64', plain,
% 12.51/12.72      (![X28 : $i, X29 : $i]:
% 12.51/12.72         ((k2_tarski @ X29 @ X28) = (k2_tarski @ X28 @ X29))),
% 12.51/12.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 12.51/12.72  thf(l51_zfmisc_1, axiom,
% 12.51/12.72    (![A:$i,B:$i]:
% 12.51/12.72     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 12.51/12.72  thf('65', plain,
% 12.51/12.72      (![X30 : $i, X31 : $i]:
% 12.51/12.72         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 12.51/12.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 12.51/12.72  thf('66', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]:
% 12.51/12.72         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 12.51/12.72      inference('sup+', [status(thm)], ['64', '65'])).
% 12.51/12.72  thf('67', plain,
% 12.51/12.72      (![X30 : $i, X31 : $i]:
% 12.51/12.72         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 12.51/12.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 12.51/12.72  thf('68', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.51/12.72      inference('sup+', [status(thm)], ['66', '67'])).
% 12.51/12.72  thf('69', plain,
% 12.51/12.72      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 12.51/12.72      inference('demod', [status(thm)], ['63', '68'])).
% 12.51/12.72  thf('70', plain,
% 12.51/12.72      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 12.51/12.72      inference('demod', [status(thm)], ['50', '69'])).
% 12.51/12.72  thf('71', plain,
% 12.51/12.72      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 12.51/12.72      inference('sup-', [status(thm)], ['21', '22'])).
% 12.51/12.72  thf('72', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 12.51/12.72      inference('sup+', [status(thm)], ['70', '71'])).
% 12.51/12.72  thf('73', plain, ($false), inference('demod', [status(thm)], ['0', '72'])).
% 12.51/12.72  
% 12.51/12.72  % SZS output end Refutation
% 12.51/12.72  
% 12.51/12.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
