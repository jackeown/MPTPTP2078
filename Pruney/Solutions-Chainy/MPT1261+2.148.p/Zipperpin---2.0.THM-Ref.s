%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ounTUfewCj

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:00 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 256 expanded)
%              Number of leaves         :   37 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          : 1233 (3164 expanded)
%              Number of equality atoms :   93 ( 190 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X32 @ X31 ) @ X31 )
      | ~ ( v4_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('61',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k2_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('74',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('75',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('82',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','83'])).

thf('85',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['65','84'])).

thf('86',plain,(
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

thf('87',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_pre_topc @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
       != X23 )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('95',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','49','50','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ounTUfewCj
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 437 iterations in 0.138s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.37/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.37/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(t77_tops_1, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.57             ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.57               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57              ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.57                ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.57                  ( k7_subset_1 @
% 0.37/0.57                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57              (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (~
% 0.37/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.57       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57             (k1_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['2'])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t69_tops_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( v4_pre_topc @ B @ A ) =>
% 0.37/0.57             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X31 : $i, X32 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.37/0.57          | (r1_tarski @ (k2_tops_1 @ X32 @ X31) @ X31)
% 0.37/0.57          | ~ (v4_pre_topc @ X31 @ X32)
% 0.37/0.57          | ~ (l1_pre_topc @ X32))),
% 0.37/0.57      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['3', '8'])).
% 0.37/0.57  thf(t28_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('11', plain,
% 0.37/0.57      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.37/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf(t100_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.57          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf(t48_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.37/0.57           = (k3_xboole_0 @ X13 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.57          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t74_tops_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( k1_tops_1 @ A @ B ) =
% 0.37/0.57             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X33 : $i, X34 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.37/0.57          | ((k1_tops_1 @ X34 @ X33)
% 0.37/0.57              = (k7_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.37/0.57                 (k2_tops_1 @ X34 @ X33)))
% 0.37/0.57          | ~ (l1_pre_topc @ X34))),
% 0.37/0.57      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.37/0.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.57  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.37/0.57          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (((k1_tops_1 @ sk_A @ sk_B)
% 0.37/0.57         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k5_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['20', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      ((((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['19', '29'])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t44_tops_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X27 : $i, X28 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.37/0.57          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ X27)
% 0.37/0.57          | ~ (l1_pre_topc @ X28))),
% 0.37/0.57      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.57  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('35', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.37/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.37/0.57         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.57         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.57         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['30', '41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57              (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (~
% 0.37/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (~
% 0.37/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.57         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= (~
% 0.37/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.57         <= (~
% 0.37/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 0.37/0.57             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['42', '47'])).
% 0.37/0.57  thf('49', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.57       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.57       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('split', [status(esa)], ['2'])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(dt_k2_tops_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.57       ( m1_subset_1 @
% 0.37/0.57         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X25 : $i, X26 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ X25)
% 0.37/0.57          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.37/0.57          | (m1_subset_1 @ (k2_tops_1 @ X25 @ X26) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.57  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('55', plain,
% 0.37/0.57      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.37/0.57  thf('56', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.37/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.37/0.57  thf('57', plain,
% 0.37/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.37/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 0.37/0.57          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.37/0.57  thf('58', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.57            = (k2_xboole_0 @ sk_B @ X0))
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.57  thf('59', plain,
% 0.37/0.57      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['55', '58'])).
% 0.37/0.57  thf('60', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t65_tops_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( k2_pre_topc @ A @ B ) =
% 0.37/0.57             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.57  thf('61', plain,
% 0.37/0.57      (![X29 : $i, X30 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.37/0.57          | ((k2_pre_topc @ X30 @ X29)
% 0.37/0.57              = (k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.37/0.57                 (k2_tops_1 @ X30 @ X29)))
% 0.37/0.57          | ~ (l1_pre_topc @ X30))),
% 0.37/0.57      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.37/0.57  thf('62', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.57            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.37/0.57  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('64', plain,
% 0.37/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.57         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['62', '63'])).
% 0.37/0.57  thf('65', plain,
% 0.37/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.37/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['59', '64'])).
% 0.37/0.57  thf('66', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.57  thf('67', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57             (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('split', [status(esa)], ['2'])).
% 0.37/0.57  thf('68', plain,
% 0.37/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.37/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['66', '67'])).
% 0.37/0.57  thf(t36_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.57  thf('69', plain,
% 0.37/0.57      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.37/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.57  thf(l32_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.57  thf('70', plain,
% 0.37/0.57      (![X2 : $i, X4 : $i]:
% 0.37/0.57         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.57  thf('71', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.37/0.57  thf('72', plain,
% 0.37/0.57      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.37/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['68', '71'])).
% 0.37/0.57  thf(t98_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.57  thf('73', plain,
% 0.37/0.57      (![X15 : $i, X16 : $i]:
% 0.37/0.57         ((k2_xboole_0 @ X15 @ X16)
% 0.37/0.57           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.37/0.57  thf('74', plain,
% 0.37/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.57          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.37/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['72', '73'])).
% 0.37/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.57  thf('75', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.57  thf('76', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('77', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.57  thf('78', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.57  thf('79', plain,
% 0.37/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['77', '78'])).
% 0.37/0.57  thf('80', plain,
% 0.37/0.57      (![X5 : $i, X6 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.57           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('81', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['79', '80'])).
% 0.37/0.57  thf(t3_boole, axiom,
% 0.37/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.57  thf('82', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.57  thf('83', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['81', '82'])).
% 0.37/0.57  thf('84', plain,
% 0.37/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.37/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('demod', [status(thm)], ['74', '83'])).
% 0.37/0.57  thf('85', plain,
% 0.37/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.37/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('sup+', [status(thm)], ['65', '84'])).
% 0.37/0.57  thf('86', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t52_pre_topc, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.37/0.57             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.37/0.57               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('87', plain,
% 0.37/0.57      (![X23 : $i, X24 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.37/0.57          | ~ (v2_pre_topc @ X24)
% 0.37/0.57          | ((k2_pre_topc @ X24 @ X23) != (X23))
% 0.37/0.57          | (v4_pre_topc @ X23 @ X24)
% 0.37/0.57          | ~ (l1_pre_topc @ X24))),
% 0.37/0.57      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.57  thf('88', plain,
% 0.37/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.57        | (v4_pre_topc @ sk_B @ sk_A)
% 0.37/0.57        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.37/0.57        | ~ (v2_pre_topc @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.37/0.57  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('90', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('91', plain,
% 0.37/0.57      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.37/0.57  thf('92', plain,
% 0.37/0.57      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.37/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['85', '91'])).
% 0.37/0.57  thf('93', plain,
% 0.37/0.57      (((v4_pre_topc @ sk_B @ sk_A))
% 0.37/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.37/0.57      inference('simplify', [status(thm)], ['92'])).
% 0.37/0.57  thf('94', plain,
% 0.37/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['0'])).
% 0.37/0.57  thf('95', plain,
% 0.37/0.57      (~
% 0.37/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.37/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.37/0.57       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['93', '94'])).
% 0.37/0.57  thf('96', plain, ($false),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['1', '49', '50', '95'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
