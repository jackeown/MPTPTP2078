%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rzrfh1Kh0C

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:32 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  198 ( 558 expanded)
%              Number of leaves         :   33 ( 181 expanded)
%              Depth                    :   26
%              Number of atoms          : 1882 (5721 expanded)
%              Number of equality atoms :  154 ( 481 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X30 )
      | ~ ( r1_tarski @ X29 @ X31 )
      | ( r1_tarski @ X29 @ ( k1_tops_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_tops_1 @ X26 @ X25 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ X25 ) @ ( k1_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('58',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('61',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('62',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('70',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','75'])).

thf('77',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('91',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','95'])).

thf('97',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79','102'])).

thf('104',plain,
    ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','103'])).

thf('105',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('106',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['104','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('114',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','75'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('118',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['116','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['115','121'])).

thf('123',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['114','122'])).

thf('124',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('125',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('127',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('129',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('131',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('132',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','129','130','131'])).

thf('133',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('134',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('137',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('139',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('143',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k1_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('144',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k7_subset_1 @ X19 @ X18 @ X20 )
        = ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145','148'])).

thf('150',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','149'])).

thf('151',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('153',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('155',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('156',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['153','159'])).

thf('161',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('162',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','32','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Rzrfh1Kh0C
% 0.16/0.36  % Computer   : n017.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.21/0.36  % CPULimit   : 60
% 0.21/0.36  % DateTime   : Tue Dec  1 15:14:02 EST 2020
% 0.21/0.36  % CPUTime    : 
% 0.21/0.36  % Running portfolio for 600 s
% 0.21/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.36  % Number of cores: 8
% 0.21/0.37  % Python version: Python 3.6.8
% 0.21/0.37  % Running in FO mode
% 1.31/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.31/1.50  % Solved by: fo/fo7.sh
% 1.31/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.31/1.50  % done 2836 iterations in 1.029s
% 1.31/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.31/1.50  % SZS output start Refutation
% 1.31/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.31/1.50  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.31/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.31/1.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.31/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.31/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.31/1.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.31/1.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.31/1.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.31/1.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.31/1.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.31/1.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.31/1.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.31/1.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.31/1.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.31/1.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.31/1.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.31/1.50  thf(t76_tops_1, conjecture,
% 1.31/1.50    (![A:$i]:
% 1.31/1.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.31/1.50       ( ![B:$i]:
% 1.31/1.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.31/1.50           ( ( v3_pre_topc @ B @ A ) <=>
% 1.31/1.50             ( ( k2_tops_1 @ A @ B ) =
% 1.31/1.50               ( k7_subset_1 @
% 1.31/1.50                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.31/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.31/1.50    (~( ![A:$i]:
% 1.31/1.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.31/1.50          ( ![B:$i]:
% 1.31/1.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.31/1.50              ( ( v3_pre_topc @ B @ A ) <=>
% 1.31/1.50                ( ( k2_tops_1 @ A @ B ) =
% 1.31/1.50                  ( k7_subset_1 @
% 1.31/1.50                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.31/1.50    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.31/1.50  thf('0', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.31/1.50        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf('1', plain,
% 1.31/1.50      (~
% 1.31/1.50       (((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.31/1.50       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.31/1.50      inference('split', [status(esa)], ['0'])).
% 1.31/1.50  thf('2', plain,
% 1.31/1.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf('3', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.31/1.50        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf('4', plain,
% 1.31/1.50      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.31/1.50      inference('split', [status(esa)], ['3'])).
% 1.31/1.50  thf('5', plain,
% 1.31/1.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf(t56_tops_1, axiom,
% 1.31/1.50    (![A:$i]:
% 1.31/1.50     ( ( l1_pre_topc @ A ) =>
% 1.31/1.50       ( ![B:$i]:
% 1.31/1.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.31/1.50           ( ![C:$i]:
% 1.31/1.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.31/1.50               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.31/1.50                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.31/1.50  thf('6', plain,
% 1.31/1.50      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.31/1.50         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.31/1.50          | ~ (v3_pre_topc @ X29 @ X30)
% 1.31/1.50          | ~ (r1_tarski @ X29 @ X31)
% 1.31/1.50          | (r1_tarski @ X29 @ (k1_tops_1 @ X30 @ X31))
% 1.31/1.50          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.31/1.50          | ~ (l1_pre_topc @ X30))),
% 1.31/1.50      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.31/1.50  thf('7', plain,
% 1.31/1.50      (![X0 : $i]:
% 1.31/1.50         (~ (l1_pre_topc @ sk_A)
% 1.31/1.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.31/1.50          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.31/1.50          | ~ (r1_tarski @ sk_B @ X0)
% 1.31/1.50          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.31/1.50      inference('sup-', [status(thm)], ['5', '6'])).
% 1.31/1.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf('9', plain,
% 1.31/1.50      (![X0 : $i]:
% 1.31/1.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.31/1.50          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.31/1.50          | ~ (r1_tarski @ sk_B @ X0)
% 1.31/1.50          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.31/1.50      inference('demod', [status(thm)], ['7', '8'])).
% 1.31/1.50  thf('10', plain,
% 1.31/1.50      ((![X0 : $i]:
% 1.31/1.50          (~ (r1_tarski @ sk_B @ X0)
% 1.31/1.50           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.31/1.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.31/1.50         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.31/1.50      inference('sup-', [status(thm)], ['4', '9'])).
% 1.31/1.50  thf('11', plain,
% 1.31/1.50      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.31/1.50         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.31/1.50      inference('sup-', [status(thm)], ['2', '10'])).
% 1.31/1.50  thf(d10_xboole_0, axiom,
% 1.31/1.50    (![A:$i,B:$i]:
% 1.31/1.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.31/1.50  thf('12', plain,
% 1.31/1.50      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.31/1.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.50  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.31/1.50      inference('simplify', [status(thm)], ['12'])).
% 1.31/1.50  thf('14', plain,
% 1.31/1.50      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.31/1.50         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.31/1.50      inference('demod', [status(thm)], ['11', '13'])).
% 1.31/1.50  thf('15', plain,
% 1.31/1.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf(t44_tops_1, axiom,
% 1.31/1.50    (![A:$i]:
% 1.31/1.50     ( ( l1_pre_topc @ A ) =>
% 1.31/1.50       ( ![B:$i]:
% 1.31/1.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.31/1.50           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.31/1.50  thf('16', plain,
% 1.31/1.50      (![X27 : $i, X28 : $i]:
% 1.31/1.50         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.31/1.50          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ X27)
% 1.31/1.50          | ~ (l1_pre_topc @ X28))),
% 1.31/1.50      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.31/1.50  thf('17', plain,
% 1.31/1.50      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.31/1.50      inference('sup-', [status(thm)], ['15', '16'])).
% 1.31/1.50  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.31/1.50      inference('demod', [status(thm)], ['17', '18'])).
% 1.31/1.50  thf('20', plain,
% 1.31/1.50      (![X2 : $i, X4 : $i]:
% 1.31/1.50         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.31/1.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.50  thf('21', plain,
% 1.31/1.50      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.31/1.50        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 1.31/1.50      inference('sup-', [status(thm)], ['19', '20'])).
% 1.31/1.50  thf('22', plain,
% 1.31/1.50      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 1.31/1.50         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.31/1.50      inference('sup-', [status(thm)], ['14', '21'])).
% 1.31/1.50  thf('23', plain,
% 1.31/1.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf(l78_tops_1, axiom,
% 1.31/1.50    (![A:$i]:
% 1.31/1.50     ( ( l1_pre_topc @ A ) =>
% 1.31/1.50       ( ![B:$i]:
% 1.31/1.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.31/1.50           ( ( k2_tops_1 @ A @ B ) =
% 1.31/1.50             ( k7_subset_1 @
% 1.31/1.50               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.31/1.50               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.31/1.50  thf('24', plain,
% 1.31/1.50      (![X25 : $i, X26 : $i]:
% 1.31/1.50         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.31/1.50          | ((k2_tops_1 @ X26 @ X25)
% 1.31/1.50              = (k7_subset_1 @ (u1_struct_0 @ X26) @ 
% 1.31/1.50                 (k2_pre_topc @ X26 @ X25) @ (k1_tops_1 @ X26 @ X25)))
% 1.31/1.50          | ~ (l1_pre_topc @ X26))),
% 1.31/1.50      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.31/1.50  thf('25', plain,
% 1.31/1.50      ((~ (l1_pre_topc @ sk_A)
% 1.31/1.50        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.31/1.50      inference('sup-', [status(thm)], ['23', '24'])).
% 1.31/1.50  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf('27', plain,
% 1.31/1.50      (((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.31/1.50            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.31/1.50      inference('demod', [status(thm)], ['25', '26'])).
% 1.31/1.50  thf('28', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.31/1.50         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.31/1.50      inference('sup+', [status(thm)], ['22', '27'])).
% 1.31/1.50  thf('29', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.31/1.50         <= (~
% 1.31/1.50             (((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.50      inference('split', [status(esa)], ['0'])).
% 1.31/1.50  thf('30', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.31/1.50         <= (~
% 1.31/1.50             (((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.31/1.50             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.31/1.50      inference('sup-', [status(thm)], ['28', '29'])).
% 1.31/1.50  thf('31', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.31/1.50       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.31/1.50      inference('simplify', [status(thm)], ['30'])).
% 1.31/1.50  thf('32', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.31/1.50       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.31/1.50      inference('split', [status(esa)], ['3'])).
% 1.31/1.50  thf('33', plain,
% 1.31/1.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf(dt_k2_pre_topc, axiom,
% 1.31/1.50    (![A:$i,B:$i]:
% 1.31/1.50     ( ( ( l1_pre_topc @ A ) & 
% 1.31/1.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.31/1.50       ( m1_subset_1 @
% 1.31/1.50         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.31/1.50  thf('34', plain,
% 1.31/1.50      (![X21 : $i, X22 : $i]:
% 1.31/1.50         (~ (l1_pre_topc @ X21)
% 1.31/1.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.31/1.50          | (m1_subset_1 @ (k2_pre_topc @ X21 @ X22) @ 
% 1.31/1.50             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 1.31/1.50      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.31/1.50  thf('35', plain,
% 1.31/1.50      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.31/1.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.31/1.50        | ~ (l1_pre_topc @ sk_A))),
% 1.31/1.50      inference('sup-', [status(thm)], ['33', '34'])).
% 1.31/1.50  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.50  thf('37', plain,
% 1.31/1.50      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.31/1.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.50      inference('demod', [status(thm)], ['35', '36'])).
% 1.31/1.50  thf(redefinition_k7_subset_1, axiom,
% 1.31/1.50    (![A:$i,B:$i,C:$i]:
% 1.31/1.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.31/1.50       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.31/1.50  thf('38', plain,
% 1.31/1.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.31/1.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.31/1.50          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 1.31/1.50      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.31/1.50  thf('39', plain,
% 1.31/1.50      (![X0 : $i]:
% 1.31/1.50         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.31/1.50           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.31/1.50      inference('sup-', [status(thm)], ['37', '38'])).
% 1.31/1.50  thf('40', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.31/1.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.50      inference('split', [status(esa)], ['3'])).
% 1.31/1.50  thf('41', plain,
% 1.31/1.50      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.31/1.50         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.50                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.50                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.50      inference('sup+', [status(thm)], ['39', '40'])).
% 1.31/1.50  thf('42', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.31/1.50      inference('simplify', [status(thm)], ['12'])).
% 1.31/1.50  thf(l32_xboole_1, axiom,
% 1.31/1.50    (![A:$i,B:$i]:
% 1.31/1.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.31/1.50  thf('43', plain,
% 1.31/1.50      (![X5 : $i, X7 : $i]:
% 1.31/1.50         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.31/1.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.31/1.50  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.31/1.50      inference('sup-', [status(thm)], ['42', '43'])).
% 1.31/1.50  thf(t41_xboole_1, axiom,
% 1.31/1.50    (![A:$i,B:$i,C:$i]:
% 1.31/1.50     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.31/1.50       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.31/1.50  thf('45', plain,
% 1.31/1.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.31/1.50           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.31/1.50      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.31/1.50  thf('46', plain,
% 1.31/1.50      (![X5 : $i, X6 : $i]:
% 1.31/1.50         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.31/1.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.31/1.50  thf('47', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.50         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 1.31/1.50          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 1.31/1.50      inference('sup-', [status(thm)], ['45', '46'])).
% 1.31/1.50  thf('48', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i]:
% 1.31/1.50         (((k1_xboole_0) != (k1_xboole_0))
% 1.31/1.50          | (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 1.31/1.50      inference('sup-', [status(thm)], ['44', '47'])).
% 1.31/1.50  thf('49', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i]:
% 1.31/1.50         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 1.31/1.50      inference('simplify', [status(thm)], ['48'])).
% 1.31/1.50  thf(t12_xboole_1, axiom,
% 1.31/1.50    (![A:$i,B:$i]:
% 1.31/1.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.31/1.50  thf('50', plain,
% 1.31/1.50      (![X8 : $i, X9 : $i]:
% 1.31/1.50         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 1.31/1.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.31/1.50  thf('51', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i]:
% 1.31/1.50         ((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 1.31/1.50           = (X0))),
% 1.31/1.50      inference('sup-', [status(thm)], ['49', '50'])).
% 1.31/1.50  thf(t48_xboole_1, axiom,
% 1.31/1.50    (![A:$i,B:$i]:
% 1.31/1.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.31/1.50  thf('52', plain,
% 1.31/1.50      (![X16 : $i, X17 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.50           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.50  thf('53', plain,
% 1.31/1.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.31/1.50           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.31/1.50      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.31/1.50  thf('54', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.31/1.50           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.31/1.50      inference('sup+', [status(thm)], ['52', '53'])).
% 1.31/1.50  thf('55', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 1.31/1.50           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.31/1.50      inference('sup+', [status(thm)], ['51', '54'])).
% 1.31/1.50  thf(commutativity_k3_xboole_0, axiom,
% 1.31/1.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.31/1.50  thf('56', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.31/1.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.31/1.50  thf('57', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.31/1.50      inference('sup-', [status(thm)], ['42', '43'])).
% 1.31/1.50  thf('58', plain,
% 1.31/1.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.31/1.50           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.31/1.50      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.31/1.50  thf('59', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.31/1.50           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.50      inference('sup+', [status(thm)], ['57', '58'])).
% 1.31/1.50  thf('60', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.31/1.50      inference('sup-', [status(thm)], ['42', '43'])).
% 1.31/1.50  thf(t3_boole, axiom,
% 1.31/1.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.31/1.50  thf('61', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.31/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.31/1.50  thf('62', plain,
% 1.31/1.50      (![X16 : $i, X17 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.50           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.50  thf('63', plain,
% 1.31/1.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.31/1.50      inference('sup+', [status(thm)], ['61', '62'])).
% 1.31/1.50  thf('64', plain,
% 1.31/1.50      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.31/1.50      inference('sup+', [status(thm)], ['60', '63'])).
% 1.31/1.50  thf('65', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.31/1.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.31/1.50  thf('66', plain,
% 1.31/1.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.31/1.50      inference('sup+', [status(thm)], ['64', '65'])).
% 1.31/1.50  thf(t47_xboole_1, axiom,
% 1.31/1.50    (![A:$i,B:$i]:
% 1.31/1.50     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.31/1.50  thf('67', plain,
% 1.31/1.50      (![X14 : $i, X15 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 1.31/1.50           = (k4_xboole_0 @ X14 @ X15))),
% 1.31/1.50      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.31/1.50  thf('68', plain,
% 1.31/1.50      (![X0 : $i]:
% 1.31/1.50         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.31/1.50           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.31/1.50      inference('sup+', [status(thm)], ['66', '67'])).
% 1.31/1.50  thf('69', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.31/1.50      inference('sup-', [status(thm)], ['42', '43'])).
% 1.31/1.50  thf('70', plain,
% 1.31/1.50      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.31/1.50      inference('demod', [status(thm)], ['68', '69'])).
% 1.31/1.50  thf('71', plain,
% 1.31/1.50      (![X0 : $i, X1 : $i]:
% 1.31/1.50         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.50      inference('demod', [status(thm)], ['59', '70'])).
% 1.31/1.51  thf('72', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('73', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 1.31/1.51           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['71', '72'])).
% 1.31/1.51  thf('74', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.31/1.51      inference('cnf', [status(esa)], [t3_boole])).
% 1.31/1.51  thf('75', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['73', '74'])).
% 1.31/1.51  thf('76', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X1 @ X0)
% 1.31/1.51           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['55', '56', '75'])).
% 1.31/1.51  thf('77', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('78', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['76', '77'])).
% 1.31/1.51  thf('79', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.31/1.51  thf('80', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('81', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('82', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['80', '81'])).
% 1.31/1.51  thf('83', plain,
% 1.31/1.51      (![X14 : $i, X15 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 1.31/1.51           = (k4_xboole_0 @ X14 @ X15))),
% 1.31/1.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.31/1.51  thf('84', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k4_xboole_0 @ X1 @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['82', '83'])).
% 1.31/1.51  thf('85', plain,
% 1.31/1.51      (![X14 : $i, X15 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 1.31/1.51           = (k4_xboole_0 @ X14 @ X15))),
% 1.31/1.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.31/1.51  thf('86', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('87', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['85', '86'])).
% 1.31/1.51  thf('88', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('89', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k3_xboole_0 @ X1 @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['87', '88'])).
% 1.31/1.51  thf('90', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.31/1.51  thf('91', plain,
% 1.31/1.51      (![X14 : $i, X15 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 1.31/1.51           = (k4_xboole_0 @ X14 @ X15))),
% 1.31/1.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.31/1.51  thf('92', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k4_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('sup+', [status(thm)], ['90', '91'])).
% 1.31/1.51  thf('93', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.31/1.51      inference('sup+', [status(thm)], ['89', '92'])).
% 1.31/1.51  thf('94', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['42', '43'])).
% 1.31/1.51  thf('95', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.31/1.51      inference('demod', [status(thm)], ['93', '94'])).
% 1.31/1.51  thf('96', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.31/1.51      inference('sup+', [status(thm)], ['84', '95'])).
% 1.31/1.51  thf('97', plain,
% 1.31/1.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 1.31/1.51           = (k4_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 1.31/1.51      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.31/1.51  thf('98', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.31/1.51      inference('demod', [status(thm)], ['96', '97'])).
% 1.31/1.51  thf('99', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('100', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 1.31/1.51           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['98', '99'])).
% 1.31/1.51  thf('101', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.31/1.51      inference('cnf', [status(esa)], [t3_boole])).
% 1.31/1.51  thf('102', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['100', '101'])).
% 1.31/1.51  thf('103', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['78', '79', '102'])).
% 1.31/1.51  thf('104', plain,
% 1.31/1.51      ((((k4_xboole_0 @ (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) @ 
% 1.31/1.51          (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['41', '103'])).
% 1.31/1.51  thf('105', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.31/1.51      inference('simplify', [status(thm)], ['12'])).
% 1.31/1.51  thf('106', plain,
% 1.31/1.51      (![X8 : $i, X9 : $i]:
% 1.31/1.51         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 1.31/1.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.31/1.51  thf('107', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['105', '106'])).
% 1.31/1.51  thf('108', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.31/1.51           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['52', '53'])).
% 1.31/1.51  thf('109', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['107', '108'])).
% 1.31/1.51  thf('110', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('111', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k3_xboole_0 @ X1 @ X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['109', '110'])).
% 1.31/1.51  thf('112', plain,
% 1.31/1.51      ((((k4_xboole_0 @ 
% 1.31/1.51          (k3_xboole_0 @ (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) @ 
% 1.31/1.51           (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.31/1.51          sk_B)
% 1.31/1.51          = (k3_xboole_0 @ 
% 1.31/1.51             (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) @ 
% 1.31/1.51             (k2_tops_1 @ sk_A @ sk_B))))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['104', '111'])).
% 1.31/1.51  thf('113', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.31/1.51  thf('114', plain,
% 1.31/1.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['39', '40'])).
% 1.31/1.51  thf('115', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X1 @ X0)
% 1.31/1.51           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['55', '56', '75'])).
% 1.31/1.51  thf('116', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.31/1.51           = (k4_xboole_0 @ X1 @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['82', '83'])).
% 1.31/1.51  thf('117', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.31/1.51      inference('demod', [status(thm)], ['93', '94'])).
% 1.31/1.51  thf('118', plain,
% 1.31/1.51      (![X5 : $i, X6 : $i]:
% 1.31/1.51         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.31/1.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.31/1.51  thf('119', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k1_xboole_0) != (k1_xboole_0))
% 1.31/1.51          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['117', '118'])).
% 1.31/1.51  thf('120', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.31/1.51      inference('simplify', [status(thm)], ['119'])).
% 1.31/1.51  thf('121', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 1.31/1.51      inference('sup+', [status(thm)], ['116', '120'])).
% 1.31/1.51  thf('122', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['115', '121'])).
% 1.31/1.51  thf('123', plain,
% 1.31/1.51      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.31/1.51         (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['114', '122'])).
% 1.31/1.51  thf('124', plain,
% 1.31/1.51      (![X5 : $i, X7 : $i]:
% 1.31/1.51         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.31/1.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.31/1.51  thf('125', plain,
% 1.31/1.51      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.31/1.51          (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (k1_xboole_0)))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup-', [status(thm)], ['123', '124'])).
% 1.31/1.51  thf('126', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('127', plain,
% 1.31/1.51      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.31/1.51          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.31/1.51             (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['125', '126'])).
% 1.31/1.51  thf('128', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.31/1.51      inference('cnf', [status(esa)], [t3_boole])).
% 1.31/1.51  thf('129', plain,
% 1.31/1.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.31/1.51             (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('demod', [status(thm)], ['127', '128'])).
% 1.31/1.51  thf('130', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.31/1.51  thf('131', plain,
% 1.31/1.51      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.31/1.51             (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('demod', [status(thm)], ['127', '128'])).
% 1.31/1.51  thf('132', plain,
% 1.31/1.51      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.31/1.51          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('demod', [status(thm)], ['112', '113', '129', '130', '131'])).
% 1.31/1.51  thf('133', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('134', plain,
% 1.31/1.51      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.31/1.51          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['132', '133'])).
% 1.31/1.51  thf('135', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['42', '43'])).
% 1.31/1.51  thf('136', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.31/1.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.31/1.51  thf('137', plain,
% 1.31/1.51      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.31/1.51  thf('138', plain,
% 1.31/1.51      (![X16 : $i, X17 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.31/1.51           = (k3_xboole_0 @ X16 @ X17))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('139', plain,
% 1.31/1.51      (![X5 : $i, X6 : $i]:
% 1.31/1.51         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.31/1.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.31/1.51  thf('140', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 1.31/1.51          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['138', '139'])).
% 1.31/1.51  thf('141', plain,
% 1.31/1.51      (((((k1_xboole_0) != (k1_xboole_0))
% 1.31/1.51         | (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup-', [status(thm)], ['137', '140'])).
% 1.31/1.51  thf('142', plain,
% 1.31/1.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf(t74_tops_1, axiom,
% 1.31/1.51    (![A:$i]:
% 1.31/1.51     ( ( l1_pre_topc @ A ) =>
% 1.31/1.51       ( ![B:$i]:
% 1.31/1.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.31/1.51           ( ( k1_tops_1 @ A @ B ) =
% 1.31/1.51             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.31/1.51  thf('143', plain,
% 1.31/1.51      (![X32 : $i, X33 : $i]:
% 1.31/1.51         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.31/1.51          | ((k1_tops_1 @ X33 @ X32)
% 1.31/1.51              = (k7_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 1.31/1.51                 (k2_tops_1 @ X33 @ X32)))
% 1.31/1.51          | ~ (l1_pre_topc @ X33))),
% 1.31/1.51      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.31/1.51  thf('144', plain,
% 1.31/1.51      ((~ (l1_pre_topc @ sk_A)
% 1.31/1.51        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.31/1.51            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.31/1.51               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.31/1.51      inference('sup-', [status(thm)], ['142', '143'])).
% 1.31/1.51  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf('146', plain,
% 1.31/1.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf('147', plain,
% 1.31/1.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.31/1.51         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.31/1.51          | ((k7_subset_1 @ X19 @ X18 @ X20) = (k4_xboole_0 @ X18 @ X20)))),
% 1.31/1.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.31/1.51  thf('148', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.31/1.51           = (k4_xboole_0 @ sk_B @ X0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['146', '147'])).
% 1.31/1.51  thf('149', plain,
% 1.31/1.51      (((k1_tops_1 @ sk_A @ sk_B)
% 1.31/1.51         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.31/1.51      inference('demod', [status(thm)], ['144', '145', '148'])).
% 1.31/1.51  thf('150', plain,
% 1.31/1.51      (((((k1_xboole_0) != (k1_xboole_0))
% 1.31/1.51         | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('demod', [status(thm)], ['141', '149'])).
% 1.31/1.51  thf('151', plain,
% 1.31/1.51      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('simplify', [status(thm)], ['150'])).
% 1.31/1.51  thf('152', plain,
% 1.31/1.51      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.31/1.51        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['19', '20'])).
% 1.31/1.51  thf('153', plain,
% 1.31/1.51      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup-', [status(thm)], ['151', '152'])).
% 1.31/1.51  thf('154', plain,
% 1.31/1.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf(fc9_tops_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.31/1.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.31/1.51       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.31/1.51  thf('155', plain,
% 1.31/1.51      (![X23 : $i, X24 : $i]:
% 1.31/1.51         (~ (l1_pre_topc @ X23)
% 1.31/1.51          | ~ (v2_pre_topc @ X23)
% 1.31/1.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.31/1.51          | (v3_pre_topc @ (k1_tops_1 @ X23 @ X24) @ X23))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.31/1.51  thf('156', plain,
% 1.31/1.51      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.31/1.51        | ~ (v2_pre_topc @ sk_A)
% 1.31/1.51        | ~ (l1_pre_topc @ sk_A))),
% 1.31/1.51      inference('sup-', [status(thm)], ['154', '155'])).
% 1.31/1.51  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf('159', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.31/1.51      inference('demod', [status(thm)], ['156', '157', '158'])).
% 1.31/1.51  thf('160', plain,
% 1.31/1.51      (((v3_pre_topc @ sk_B @ sk_A))
% 1.31/1.51         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['153', '159'])).
% 1.31/1.51  thf('161', plain,
% 1.31/1.51      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.31/1.51      inference('split', [status(esa)], ['0'])).
% 1.31/1.51  thf('162', plain,
% 1.31/1.51      (~
% 1.31/1.51       (((k2_tops_1 @ sk_A @ sk_B)
% 1.31/1.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.31/1.51             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.31/1.51       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.31/1.51      inference('sup-', [status(thm)], ['160', '161'])).
% 1.31/1.51  thf('163', plain, ($false),
% 1.31/1.51      inference('sat_resolution*', [status(thm)], ['1', '31', '32', '162'])).
% 1.31/1.51  
% 1.31/1.51  % SZS output end Refutation
% 1.31/1.51  
% 1.31/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
