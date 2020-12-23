%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DyBgfVH9jZ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:57 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 301 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          : 1053 (4026 expanded)
%              Number of equality atoms :   64 ( 211 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ ( k2_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['11','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('41',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','44'])).

thf('46',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['6','47'])).

thf('49',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['5','48'])).

thf('50',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('51',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('52',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('54',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X30 @ X29 ) @ X29 )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('65',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('68',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('70',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['50','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('74',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_tops_1 @ X26 @ X25 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ X25 ) @ ( k1_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('82',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['6','47','81'])).

thf('83',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','83'])).

thf('85',plain,(
    $false ),
    inference(simplify,[status(thm)],['84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DyBgfVH9jZ
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:32:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 646 iterations in 0.252s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.50/0.72  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.50/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.72  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.50/0.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.50/0.72  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.50/0.72  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.50/0.72  thf(t77_tops_1, conjecture,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.72       ( ![B:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72           ( ( v4_pre_topc @ B @ A ) <=>
% 0.50/0.72             ( ( k2_tops_1 @ A @ B ) =
% 0.50/0.72               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i]:
% 0.50/0.72        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.72          ( ![B:$i]:
% 0.50/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72              ( ( v4_pre_topc @ B @ A ) <=>
% 0.50/0.72                ( ( k2_tops_1 @ A @ B ) =
% 0.50/0.72                  ( k7_subset_1 @
% 0.50/0.72                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.50/0.72  thf('0', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72              (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.72        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('1', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72              (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= (~
% 0.50/0.72             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('split', [status(esa)], ['0'])).
% 0.50/0.72  thf('2', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(redefinition_k7_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.50/0.72  thf('3', plain,
% 0.50/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.50/0.72          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.50/0.72      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.50/0.72  thf('4', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.72           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('5', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= (~
% 0.50/0.72             (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('demod', [status(thm)], ['1', '4'])).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      (~
% 0.50/0.72       (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.50/0.72       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.72      inference('split', [status(esa)], ['0'])).
% 0.50/0.72  thf('7', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t65_tops_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( l1_pre_topc @ A ) =>
% 0.50/0.72       ( ![B:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72           ( ( k2_pre_topc @ A @ B ) =
% 0.50/0.72             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.50/0.72  thf('8', plain,
% 0.50/0.72      (![X27 : $i, X28 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.50/0.72          | ((k2_pre_topc @ X28 @ X27)
% 0.50/0.72              = (k4_subset_1 @ (u1_struct_0 @ X28) @ X27 @ 
% 0.50/0.72                 (k2_tops_1 @ X28 @ X27)))
% 0.50/0.72          | ~ (l1_pre_topc @ X28))),
% 0.50/0.72      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.50/0.72  thf('9', plain,
% 0.50/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.72        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.72            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.50/0.72  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('11', plain,
% 0.50/0.72      (((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.72         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.50/0.72  thf('12', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.72           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72             (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.72        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('14', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72             (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('split', [status(esa)], ['13'])).
% 0.50/0.72  thf('15', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('sup+', [status(thm)], ['12', '14'])).
% 0.50/0.72  thf('16', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t3_subset, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.72  thf('17', plain,
% 0.50/0.72      (![X20 : $i, X21 : $i]:
% 0.50/0.72         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.50/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.72  thf('18', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.50/0.72  thf(t36_xboole_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.50/0.72  thf('19', plain,
% 0.50/0.72      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.50/0.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.50/0.72  thf(t1_xboole_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.50/0.72       ( r1_tarski @ A @ C ) ))).
% 0.50/0.72  thf('20', plain,
% 0.50/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.72         (~ (r1_tarski @ X6 @ X7)
% 0.50/0.72          | ~ (r1_tarski @ X7 @ X8)
% 0.50/0.72          | (r1_tarski @ X6 @ X8))),
% 0.50/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.50/0.72  thf('21', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.72         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.72      inference('sup-', [status(thm)], ['19', '20'])).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['18', '21'])).
% 0.50/0.72  thf('23', plain,
% 0.50/0.72      (![X20 : $i, X22 : $i]:
% 0.50/0.72         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.50/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.50/0.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.50/0.72  thf('25', plain,
% 0.50/0.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('sup+', [status(thm)], ['15', '24'])).
% 0.50/0.72  thf('26', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(redefinition_k4_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.50/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.50/0.72       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.50/0.72  thf('27', plain,
% 0.50/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.50/0.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 0.50/0.72          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 0.50/0.72      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.50/0.72  thf('28', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.72            = (k2_xboole_0 @ sk_B @ X0))
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.72  thf('29', plain,
% 0.50/0.72      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.72          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['25', '28'])).
% 0.50/0.72  thf('30', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('sup+', [status(thm)], ['12', '14'])).
% 0.50/0.72  thf('31', plain,
% 0.50/0.72      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.50/0.72      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.50/0.72  thf(t12_xboole_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.50/0.72  thf('32', plain,
% 0.50/0.72      (![X4 : $i, X5 : $i]:
% 0.50/0.72         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.50/0.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.72  thf('33', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.72  thf(commutativity_k2_xboole_0, axiom,
% 0.50/0.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.50/0.72  thf('34', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.72  thf('35', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]:
% 0.50/0.72         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.50/0.72      inference('demod', [status(thm)], ['33', '34'])).
% 0.50/0.72  thf('36', plain,
% 0.50/0.72      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('sup+', [status(thm)], ['30', '35'])).
% 0.50/0.72  thf('37', plain,
% 0.50/0.72      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.72          = (sk_B)))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('demod', [status(thm)], ['29', '36'])).
% 0.50/0.72  thf('38', plain,
% 0.50/0.72      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('sup+', [status(thm)], ['11', '37'])).
% 0.50/0.72  thf('39', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(fc1_tops_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.50/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.72       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.50/0.72  thf('40', plain,
% 0.50/0.72      (![X23 : $i, X24 : $i]:
% 0.50/0.72         (~ (l1_pre_topc @ X23)
% 0.50/0.72          | ~ (v2_pre_topc @ X23)
% 0.50/0.72          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.50/0.72          | (v4_pre_topc @ (k2_pre_topc @ X23 @ X24) @ X23))),
% 0.50/0.72      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.50/0.72  thf('41', plain,
% 0.50/0.72      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.50/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.50/0.72  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('44', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.50/0.72      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.50/0.72  thf('45', plain,
% 0.50/0.72      (((v4_pre_topc @ sk_B @ sk_A))
% 0.50/0.72         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.50/0.72      inference('sup+', [status(thm)], ['38', '44'])).
% 0.50/0.72  thf('46', plain,
% 0.50/0.72      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('split', [status(esa)], ['0'])).
% 0.50/0.72  thf('47', plain,
% 0.50/0.72      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.50/0.72       ~
% 0.50/0.72       (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.72  thf('48', plain,
% 0.50/0.72      (~
% 0.50/0.72       (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.72      inference('sat_resolution*', [status(thm)], ['6', '47'])).
% 0.50/0.72  thf('49', plain,
% 0.50/0.72      (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('simpl_trail', [status(thm)], ['5', '48'])).
% 0.50/0.72  thf('50', plain,
% 0.50/0.72      (((k2_pre_topc @ sk_A @ sk_B)
% 0.50/0.72         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.50/0.72  thf('51', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.50/0.72  thf('52', plain,
% 0.50/0.72      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('split', [status(esa)], ['13'])).
% 0.50/0.72  thf('53', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t69_tops_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( l1_pre_topc @ A ) =>
% 0.50/0.72       ( ![B:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72           ( ( v4_pre_topc @ B @ A ) =>
% 0.50/0.72             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.50/0.72  thf('54', plain,
% 0.50/0.72      (![X29 : $i, X30 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.50/0.72          | (r1_tarski @ (k2_tops_1 @ X30 @ X29) @ X29)
% 0.50/0.72          | ~ (v4_pre_topc @ X29 @ X30)
% 0.50/0.72          | ~ (l1_pre_topc @ X30))),
% 0.50/0.72      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.50/0.72  thf('55', plain,
% 0.50/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.72        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.50/0.72        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.72      inference('sup-', [status(thm)], ['53', '54'])).
% 0.50/0.72  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('57', plain,
% 0.50/0.72      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.50/0.72        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.72      inference('demod', [status(thm)], ['55', '56'])).
% 0.50/0.72  thf('58', plain,
% 0.50/0.72      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['52', '57'])).
% 0.50/0.72  thf('59', plain,
% 0.50/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.72         (~ (r1_tarski @ X6 @ X7)
% 0.50/0.72          | ~ (r1_tarski @ X7 @ X8)
% 0.50/0.72          | (r1_tarski @ X6 @ X8))),
% 0.50/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.50/0.72  thf('60', plain,
% 0.50/0.72      ((![X0 : $i]:
% 0.50/0.72          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.50/0.72           | ~ (r1_tarski @ sk_B @ X0)))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['58', '59'])).
% 0.50/0.72  thf('61', plain,
% 0.50/0.72      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['51', '60'])).
% 0.50/0.72  thf('62', plain,
% 0.50/0.72      (![X20 : $i, X22 : $i]:
% 0.50/0.72         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.50/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.72  thf('63', plain,
% 0.50/0.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['61', '62'])).
% 0.50/0.72  thf('64', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.72            = (k2_xboole_0 @ sk_B @ X0))
% 0.50/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.72  thf('65', plain,
% 0.50/0.72      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.72          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['63', '64'])).
% 0.50/0.72  thf('66', plain,
% 0.50/0.72      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['52', '57'])).
% 0.50/0.72  thf('67', plain,
% 0.50/0.72      (![X4 : $i, X5 : $i]:
% 0.50/0.72         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.50/0.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.50/0.72  thf('68', plain,
% 0.50/0.72      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['66', '67'])).
% 0.50/0.72  thf('69', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.72  thf('70', plain,
% 0.50/0.72      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['68', '69'])).
% 0.50/0.72  thf('71', plain,
% 0.50/0.72      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.50/0.72          = (sk_B)))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['65', '70'])).
% 0.50/0.72  thf('72', plain,
% 0.50/0.72      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup+', [status(thm)], ['50', '71'])).
% 0.50/0.72  thf('73', plain,
% 0.50/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(l78_tops_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( l1_pre_topc @ A ) =>
% 0.50/0.72       ( ![B:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.72           ( ( k2_tops_1 @ A @ B ) =
% 0.50/0.72             ( k7_subset_1 @
% 0.50/0.72               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.50/0.72               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.50/0.72  thf('74', plain,
% 0.50/0.72      (![X25 : $i, X26 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.50/0.72          | ((k2_tops_1 @ X26 @ X25)
% 0.50/0.72              = (k7_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.50/0.72                 (k2_pre_topc @ X26 @ X25) @ (k1_tops_1 @ X26 @ X25)))
% 0.50/0.72          | ~ (l1_pre_topc @ X26))),
% 0.50/0.72      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.50/0.72  thf('75', plain,
% 0.50/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.72        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.50/0.72               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.72      inference('sup-', [status(thm)], ['73', '74'])).
% 0.50/0.72  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('77', plain,
% 0.50/0.72      (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.50/0.72            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('demod', [status(thm)], ['75', '76'])).
% 0.50/0.72  thf('78', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72             (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('sup+', [status(thm)], ['72', '77'])).
% 0.50/0.72  thf('79', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.50/0.72           = (k4_xboole_0 @ sk_B @ X0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf('80', plain,
% 0.50/0.72      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.50/0.72         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['78', '79'])).
% 0.50/0.72  thf('81', plain,
% 0.50/0.72      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.50/0.72       (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.50/0.72             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.50/0.72      inference('split', [status(esa)], ['13'])).
% 0.50/0.72  thf('82', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.50/0.72      inference('sat_resolution*', [status(thm)], ['6', '47', '81'])).
% 0.50/0.72  thf('83', plain,
% 0.50/0.72      (((k2_tops_1 @ sk_A @ sk_B)
% 0.50/0.72         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.50/0.72      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.50/0.72  thf('84', plain, (((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.50/0.72      inference('demod', [status(thm)], ['49', '83'])).
% 0.50/0.72  thf('85', plain, ($false), inference('simplify', [status(thm)], ['84'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.59/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
