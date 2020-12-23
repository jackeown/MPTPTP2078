%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9VXYJ2Qk0z

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 347 expanded)
%              Number of leaves         :   31 ( 114 expanded)
%              Depth                    :   23
%              Number of atoms          : 1027 (4131 expanded)
%              Number of equality atoms :   65 ( 214 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_tops_1 @ X26 @ X25 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ X25 ) @ ( k1_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X5 ) @ ( k4_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X30 @ X29 ) @ X29 )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ ( k2_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X3 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X2 ) @ X0 ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','50'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('55',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('59',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','62'])).

thf('64',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('65',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('67',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['18','65','66'])).

thf('68',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['16','67'])).

thf('69',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['14','68'])).

thf('70',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X5 ) @ ( k4_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('78',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','31'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('82',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','80','81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['17'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['18','65'])).

thf('87',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9VXYJ2Qk0z
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 158 iterations in 0.067s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.52  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(t77_tops_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.52             ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.52               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52              ( ( v4_pre_topc @ B @ A ) <=>
% 0.21/0.52                ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.52                  ( k7_subset_1 @
% 0.21/0.52                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(l78_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.52             ( k7_subset_1 @
% 0.21/0.52               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.52               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X25 : $i, X26 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.52          | ((k2_tops_1 @ X26 @ X25)
% 0.21/0.52              = (k7_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.21/0.52                 (k2_pre_topc @ X26 @ X25) @ (k1_tops_1 @ X26 @ X25)))
% 0.21/0.52          | ~ (l1_pre_topc @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.52               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.52            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(t36_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.21/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.52  thf(t34_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.52          | (r1_tarski @ (k4_xboole_0 @ X6 @ X5) @ (k4_xboole_0 @ X6 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 0.21/0.52          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t38_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.21/0.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (((X9) = (k1_xboole_0))
% 0.21/0.52          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.21/0.52  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t69_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.52             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X29 : $i, X30 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.21/0.52          | (r1_tarski @ (k2_tops_1 @ X30 @ X29) @ X29)
% 0.21/0.52          | ~ (v4_pre_topc @ X29 @ X30)
% 0.21/0.52          | ~ (l1_pre_topc @ X30))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.21/0.52        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.21/0.52        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52             (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.52        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52              (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.52        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (~
% 0.21/0.52       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.21/0.52       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t65_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( k2_pre_topc @ A @ B ) =
% 0.21/0.52             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.52          | ((k2_pre_topc @ X28 @ X27)
% 0.21/0.52              = (k4_subset_1 @ (u1_struct_0 @ X28) @ X27 @ 
% 0.21/0.52                 (k2_tops_1 @ X28 @ X27)))
% 0.21/0.52          | ~ (l1_pre_topc @ X28))),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.52            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k2_tops_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X21 : $i, X22 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X21)
% 0.21/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.52          | (m1_subset_1 @ (k2_tops_1 @ X21 @ X22) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.52       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.21/0.52          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.52            = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.52         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.52         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.21/0.52          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.52           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52             (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 0.21/0.52          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf(t1_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.52       ( r1_tarski @ A @ C ) ))).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X1 @ X2)
% 0.21/0.52          | ~ (r1_tarski @ X2 @ X3)
% 0.21/0.52          | (r1_tarski @ X1 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X3)
% 0.21/0.52          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X3))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.21/0.52          | (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X2) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.52  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.21/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.52  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X2) @ X0)),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '45'])).
% 0.21/0.52  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i]:
% 0.21/0.52         (((X9) = (k1_xboole_0))
% 0.21/0.52          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.21/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['37', '50'])).
% 0.21/0.52  thf(t39_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.21/0.52           = (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.21/0.52          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf(t1_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['32', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(fc1_tops_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X23)
% 0.21/0.52          | ~ (v2_pre_topc @ X23)
% 0.21/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.21/0.52          | (v4_pre_topc @ (k2_pre_topc @ X23 @ X24) @ X23))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_B @ sk_A))
% 0.21/0.52         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['56', '62'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.52       ~
% 0.21/0.52       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.52       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.52      inference('split', [status(esa)], ['15'])).
% 0.21/0.52  thf('67', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['18', '65', '66'])).
% 0.21/0.52  thf('68', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['16', '67'])).
% 0.21/0.52  thf('69', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '68'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.52          | (r1_tarski @ (k4_xboole_0 @ X6 @ X5) @ (k4_xboole_0 @ X6 @ X4)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ 
% 0.21/0.52          (k4_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      ((r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52        k1_xboole_0)),
% 0.21/0.52      inference('sup+', [status(thm)], ['9', '71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i]:
% 0.21/0.52         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.21/0.52           = (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.21/0.52         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['74', '75'])).
% 0.21/0.52  thf('77', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.52         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '22', '31'])).
% 0.21/0.52  thf('80', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.52      inference('sup+', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.52           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '80', '81'])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52              (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('split', [status(esa)], ['17'])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.52           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.21/0.52         <= (~
% 0.21/0.52             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.21/0.52      inference('demod', [status(thm)], ['83', '84'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (~
% 0.21/0.52       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['18', '65'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.52         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.21/0.52  thf('88', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['82', '87'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
