%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pq6mSYiVSN

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:29 EST 2020

% Result     : Theorem 5.62s
% Output     : Refutation 5.68s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 284 expanded)
%              Number of leaves         :   40 (  97 expanded)
%              Depth                    :   15
%              Number of atoms          : 1467 (3351 expanded)
%              Number of equality atoms :   84 ( 174 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( v3_pre_topc @ X64 @ X65 )
      | ~ ( r1_tarski @ X64 @ X66 )
      | ( r1_tarski @ X64 @ ( k1_tops_1 @ X65 @ X66 ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X65 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) )
      | ( ( k1_tops_1 @ X72 @ X71 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X72 ) @ X71 @ ( k2_tops_1 @ X72 @ X71 ) ) )
      | ~ ( l1_pre_topc @ X72 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k2_tops_1 @ X63 @ X62 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X63 ) @ ( k2_pre_topc @ X63 @ X62 ) @ ( k1_tops_1 @ X63 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( l1_pre_topc @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X58 @ X59 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X33 @ X32 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ( ( k2_pre_topc @ X70 @ X69 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X70 ) @ X69 @ ( k2_tops_1 @ X70 @ X69 ) ) )
      | ~ ( l1_pre_topc @ X70 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('63',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('66',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('67',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('70',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( ( k7_subset_1 @ X47 @ X48 @ X46 )
        = ( k9_subset_1 @ X47 @ X48 @ ( k3_subset_1 @ X47 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('73',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X39 @ ( k3_subset_1 @ X39 @ X38 ) )
        = X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('76',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('81',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('85',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['74','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('95',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X2 )
      = ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('98',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('100',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k9_subset_1 @ X36 @ X35 @ X35 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['93','96','101'])).

thf('103',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','102'])).

thf('104',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('105',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('107',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X60 @ X61 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('108',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['105','111'])).

thf('113',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pq6mSYiVSN
% 0.13/0.37  % Computer   : n016.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 11:49:19 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 5.62/5.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.62/5.85  % Solved by: fo/fo7.sh
% 5.62/5.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.62/5.85  % done 12449 iterations in 5.369s
% 5.62/5.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.62/5.85  % SZS output start Refutation
% 5.62/5.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.62/5.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.62/5.85  thf(sk_A_type, type, sk_A: $i).
% 5.62/5.85  thf(sk_B_type, type, sk_B: $i).
% 5.62/5.85  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.62/5.85  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.62/5.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.62/5.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.62/5.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.62/5.85  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 5.62/5.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.62/5.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.62/5.85  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.62/5.85  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.62/5.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.62/5.85  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.62/5.85  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.62/5.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.62/5.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.62/5.85  thf(t76_tops_1, conjecture,
% 5.62/5.85    (![A:$i]:
% 5.62/5.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.62/5.85       ( ![B:$i]:
% 5.62/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.62/5.85           ( ( v3_pre_topc @ B @ A ) <=>
% 5.62/5.85             ( ( k2_tops_1 @ A @ B ) =
% 5.62/5.85               ( k7_subset_1 @
% 5.62/5.85                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 5.62/5.85  thf(zf_stmt_0, negated_conjecture,
% 5.62/5.85    (~( ![A:$i]:
% 5.62/5.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.62/5.85          ( ![B:$i]:
% 5.62/5.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.62/5.85              ( ( v3_pre_topc @ B @ A ) <=>
% 5.62/5.85                ( ( k2_tops_1 @ A @ B ) =
% 5.62/5.85                  ( k7_subset_1 @
% 5.62/5.85                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 5.62/5.85    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 5.62/5.85  thf('0', plain,
% 5.62/5.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 5.62/5.85        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf('1', plain,
% 5.62/5.85      (~
% 5.62/5.85       (((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 5.62/5.85       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 5.62/5.85      inference('split', [status(esa)], ['0'])).
% 5.62/5.85  thf('2', plain,
% 5.62/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf('3', plain,
% 5.62/5.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 5.62/5.85        | (v3_pre_topc @ sk_B @ sk_A))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf('4', plain,
% 5.62/5.85      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.62/5.85      inference('split', [status(esa)], ['3'])).
% 5.62/5.85  thf('5', plain,
% 5.62/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf(t56_tops_1, axiom,
% 5.62/5.85    (![A:$i]:
% 5.62/5.85     ( ( l1_pre_topc @ A ) =>
% 5.62/5.85       ( ![B:$i]:
% 5.62/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.62/5.85           ( ![C:$i]:
% 5.62/5.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.62/5.85               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 5.62/5.85                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 5.62/5.85  thf('6', plain,
% 5.62/5.85      (![X64 : $i, X65 : $i, X66 : $i]:
% 5.62/5.85         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 5.62/5.85          | ~ (v3_pre_topc @ X64 @ X65)
% 5.62/5.85          | ~ (r1_tarski @ X64 @ X66)
% 5.62/5.85          | (r1_tarski @ X64 @ (k1_tops_1 @ X65 @ X66))
% 5.62/5.85          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 5.62/5.85          | ~ (l1_pre_topc @ X65))),
% 5.62/5.85      inference('cnf', [status(esa)], [t56_tops_1])).
% 5.62/5.85  thf('7', plain,
% 5.62/5.85      (![X0 : $i]:
% 5.62/5.85         (~ (l1_pre_topc @ sk_A)
% 5.62/5.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.62/5.85          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 5.62/5.85          | ~ (r1_tarski @ sk_B @ X0)
% 5.62/5.85          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 5.62/5.85      inference('sup-', [status(thm)], ['5', '6'])).
% 5.62/5.85  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf('9', plain,
% 5.62/5.85      (![X0 : $i]:
% 5.62/5.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.62/5.85          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 5.62/5.85          | ~ (r1_tarski @ sk_B @ X0)
% 5.62/5.85          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 5.62/5.85      inference('demod', [status(thm)], ['7', '8'])).
% 5.62/5.85  thf('10', plain,
% 5.62/5.85      ((![X0 : $i]:
% 5.62/5.85          (~ (r1_tarski @ sk_B @ X0)
% 5.62/5.85           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 5.62/5.85           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 5.62/5.85         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.62/5.85      inference('sup-', [status(thm)], ['4', '9'])).
% 5.62/5.85  thf('11', plain,
% 5.62/5.85      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.62/5.85         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.62/5.85      inference('sup-', [status(thm)], ['2', '10'])).
% 5.62/5.85  thf(d10_xboole_0, axiom,
% 5.62/5.85    (![A:$i,B:$i]:
% 5.62/5.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.62/5.85  thf('12', plain,
% 5.62/5.85      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 5.62/5.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.62/5.85  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 5.62/5.85      inference('simplify', [status(thm)], ['12'])).
% 5.62/5.85  thf('14', plain,
% 5.62/5.85      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 5.62/5.85         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.62/5.85      inference('demod', [status(thm)], ['11', '13'])).
% 5.62/5.85  thf('15', plain,
% 5.62/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf(t74_tops_1, axiom,
% 5.62/5.85    (![A:$i]:
% 5.62/5.85     ( ( l1_pre_topc @ A ) =>
% 5.62/5.85       ( ![B:$i]:
% 5.62/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.62/5.85           ( ( k1_tops_1 @ A @ B ) =
% 5.62/5.85             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.62/5.85  thf('16', plain,
% 5.62/5.85      (![X71 : $i, X72 : $i]:
% 5.62/5.85         (~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 5.62/5.85          | ((k1_tops_1 @ X72 @ X71)
% 5.62/5.85              = (k7_subset_1 @ (u1_struct_0 @ X72) @ X71 @ 
% 5.62/5.85                 (k2_tops_1 @ X72 @ X71)))
% 5.62/5.85          | ~ (l1_pre_topc @ X72))),
% 5.62/5.85      inference('cnf', [status(esa)], [t74_tops_1])).
% 5.62/5.85  thf('17', plain,
% 5.62/5.85      ((~ (l1_pre_topc @ sk_A)
% 5.62/5.85        | ((k1_tops_1 @ sk_A @ sk_B)
% 5.62/5.85            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.62/5.85               (k2_tops_1 @ sk_A @ sk_B))))),
% 5.62/5.85      inference('sup-', [status(thm)], ['15', '16'])).
% 5.62/5.85  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf('19', plain,
% 5.62/5.85      (((k1_tops_1 @ sk_A @ sk_B)
% 5.62/5.85         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.62/5.85            (k2_tops_1 @ sk_A @ sk_B)))),
% 5.62/5.85      inference('demod', [status(thm)], ['17', '18'])).
% 5.62/5.85  thf('20', plain,
% 5.62/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf(redefinition_k7_subset_1, axiom,
% 5.62/5.85    (![A:$i,B:$i,C:$i]:
% 5.62/5.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.62/5.85       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 5.62/5.85  thf('21', plain,
% 5.62/5.85      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.62/5.85         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 5.62/5.85          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 5.62/5.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 5.62/5.85  thf('22', plain,
% 5.62/5.85      (![X0 : $i]:
% 5.62/5.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 5.62/5.85           = (k4_xboole_0 @ sk_B @ X0))),
% 5.62/5.85      inference('sup-', [status(thm)], ['20', '21'])).
% 5.62/5.85  thf('23', plain,
% 5.62/5.85      (((k1_tops_1 @ sk_A @ sk_B)
% 5.62/5.85         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.62/5.85      inference('demod', [status(thm)], ['19', '22'])).
% 5.62/5.85  thf(t36_xboole_1, axiom,
% 5.62/5.85    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.62/5.85  thf('24', plain,
% 5.62/5.85      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 5.62/5.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.62/5.85  thf('25', plain,
% 5.62/5.85      (![X4 : $i, X6 : $i]:
% 5.62/5.85         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 5.62/5.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.62/5.85  thf('26', plain,
% 5.62/5.85      (![X0 : $i, X1 : $i]:
% 5.62/5.85         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 5.62/5.85          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.62/5.85      inference('sup-', [status(thm)], ['24', '25'])).
% 5.62/5.85  thf('27', plain,
% 5.62/5.85      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.62/5.85        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 5.62/5.85      inference('sup-', [status(thm)], ['23', '26'])).
% 5.62/5.85  thf('28', plain,
% 5.62/5.85      (((k1_tops_1 @ sk_A @ sk_B)
% 5.62/5.85         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.62/5.85      inference('demod', [status(thm)], ['19', '22'])).
% 5.62/5.85  thf('29', plain,
% 5.62/5.85      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 5.62/5.85        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 5.62/5.85      inference('demod', [status(thm)], ['27', '28'])).
% 5.62/5.85  thf('30', plain,
% 5.62/5.85      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 5.62/5.85         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.62/5.85      inference('sup-', [status(thm)], ['14', '29'])).
% 5.62/5.85  thf('31', plain,
% 5.62/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf(l78_tops_1, axiom,
% 5.62/5.85    (![A:$i]:
% 5.62/5.85     ( ( l1_pre_topc @ A ) =>
% 5.62/5.85       ( ![B:$i]:
% 5.62/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.62/5.85           ( ( k2_tops_1 @ A @ B ) =
% 5.62/5.85             ( k7_subset_1 @
% 5.62/5.85               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 5.62/5.85               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.62/5.85  thf('32', plain,
% 5.62/5.85      (![X62 : $i, X63 : $i]:
% 5.62/5.85         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 5.62/5.85          | ((k2_tops_1 @ X63 @ X62)
% 5.62/5.85              = (k7_subset_1 @ (u1_struct_0 @ X63) @ 
% 5.62/5.85                 (k2_pre_topc @ X63 @ X62) @ (k1_tops_1 @ X63 @ X62)))
% 5.62/5.85          | ~ (l1_pre_topc @ X63))),
% 5.62/5.85      inference('cnf', [status(esa)], [l78_tops_1])).
% 5.62/5.85  thf('33', plain,
% 5.62/5.85      ((~ (l1_pre_topc @ sk_A)
% 5.62/5.85        | ((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.62/5.85      inference('sup-', [status(thm)], ['31', '32'])).
% 5.62/5.85  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf('35', plain,
% 5.62/5.85      (((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.62/5.85            (k1_tops_1 @ sk_A @ sk_B)))),
% 5.62/5.85      inference('demod', [status(thm)], ['33', '34'])).
% 5.62/5.85  thf('36', plain,
% 5.62/5.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 5.62/5.85         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 5.62/5.85      inference('sup+', [status(thm)], ['30', '35'])).
% 5.62/5.85  thf('37', plain,
% 5.62/5.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 5.62/5.85         <= (~
% 5.62/5.85             (((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 5.62/5.85      inference('split', [status(esa)], ['0'])).
% 5.62/5.85  thf('38', plain,
% 5.62/5.85      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 5.62/5.85         <= (~
% 5.62/5.85             (((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 5.62/5.85             ((v3_pre_topc @ sk_B @ sk_A)))),
% 5.62/5.85      inference('sup-', [status(thm)], ['36', '37'])).
% 5.62/5.85  thf('39', plain,
% 5.62/5.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 5.62/5.85       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 5.62/5.85      inference('simplify', [status(thm)], ['38'])).
% 5.62/5.85  thf('40', plain,
% 5.62/5.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.62/5.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.62/5.85             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 5.62/5.85       ((v3_pre_topc @ sk_B @ sk_A))),
% 5.62/5.85      inference('split', [status(esa)], ['3'])).
% 5.62/5.85  thf('41', plain,
% 5.62/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf(dt_k2_tops_1, axiom,
% 5.62/5.85    (![A:$i,B:$i]:
% 5.62/5.85     ( ( ( l1_pre_topc @ A ) & 
% 5.62/5.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.62/5.85       ( m1_subset_1 @
% 5.62/5.85         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.62/5.85  thf('42', plain,
% 5.62/5.85      (![X58 : $i, X59 : $i]:
% 5.62/5.85         (~ (l1_pre_topc @ X58)
% 5.62/5.85          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 5.62/5.85          | (m1_subset_1 @ (k2_tops_1 @ X58 @ X59) @ 
% 5.62/5.85             (k1_zfmisc_1 @ (u1_struct_0 @ X58))))),
% 5.62/5.85      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 5.62/5.85  thf('43', plain,
% 5.62/5.85      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.62/5.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.62/5.85        | ~ (l1_pre_topc @ sk_A))),
% 5.62/5.85      inference('sup-', [status(thm)], ['41', '42'])).
% 5.62/5.85  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.62/5.85  thf('45', plain,
% 5.62/5.85      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.62/5.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.62/5.85      inference('demod', [status(thm)], ['43', '44'])).
% 5.62/5.85  thf('46', plain,
% 5.62/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.62/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf(dt_k4_subset_1, axiom,
% 5.68/5.85    (![A:$i,B:$i,C:$i]:
% 5.68/5.85     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.68/5.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.68/5.85       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 5.68/5.85  thf('47', plain,
% 5.68/5.85      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.68/5.85         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 5.68/5.85          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 5.68/5.85          | (m1_subset_1 @ (k4_subset_1 @ X33 @ X32 @ X34) @ 
% 5.68/5.85             (k1_zfmisc_1 @ X33)))),
% 5.68/5.85      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 5.68/5.85  thf('48', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 5.68/5.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.68/5.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.68/5.85      inference('sup-', [status(thm)], ['46', '47'])).
% 5.68/5.85  thf('49', plain,
% 5.68/5.85      ((m1_subset_1 @ 
% 5.68/5.85        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 5.68/5.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['45', '48'])).
% 5.68/5.85  thf('50', plain,
% 5.68/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf(t65_tops_1, axiom,
% 5.68/5.85    (![A:$i]:
% 5.68/5.85     ( ( l1_pre_topc @ A ) =>
% 5.68/5.85       ( ![B:$i]:
% 5.68/5.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.68/5.85           ( ( k2_pre_topc @ A @ B ) =
% 5.68/5.85             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.68/5.85  thf('51', plain,
% 5.68/5.85      (![X69 : $i, X70 : $i]:
% 5.68/5.85         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 5.68/5.85          | ((k2_pre_topc @ X70 @ X69)
% 5.68/5.85              = (k4_subset_1 @ (u1_struct_0 @ X70) @ X69 @ 
% 5.68/5.85                 (k2_tops_1 @ X70 @ X69)))
% 5.68/5.85          | ~ (l1_pre_topc @ X70))),
% 5.68/5.85      inference('cnf', [status(esa)], [t65_tops_1])).
% 5.68/5.85  thf('52', plain,
% 5.68/5.85      ((~ (l1_pre_topc @ sk_A)
% 5.68/5.85        | ((k2_pre_topc @ sk_A @ sk_B)
% 5.68/5.85            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.68/5.85               (k2_tops_1 @ sk_A @ sk_B))))),
% 5.68/5.85      inference('sup-', [status(thm)], ['50', '51'])).
% 5.68/5.85  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('54', plain,
% 5.68/5.85      (((k2_pre_topc @ sk_A @ sk_B)
% 5.68/5.85         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 5.68/5.85            (k2_tops_1 @ sk_A @ sk_B)))),
% 5.68/5.85      inference('demod', [status(thm)], ['52', '53'])).
% 5.68/5.85  thf('55', plain,
% 5.68/5.85      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.68/5.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.68/5.85      inference('demod', [status(thm)], ['49', '54'])).
% 5.68/5.85  thf('56', plain,
% 5.68/5.85      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.68/5.85         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 5.68/5.85          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 5.68/5.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 5.68/5.85  thf('57', plain,
% 5.68/5.85      (![X0 : $i]:
% 5.68/5.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.68/5.85           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['55', '56'])).
% 5.68/5.85  thf('58', plain,
% 5.68/5.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.68/5.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.68/5.85             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 5.68/5.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.68/5.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.68/5.85                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 5.68/5.85      inference('split', [status(esa)], ['3'])).
% 5.68/5.85  thf('59', plain,
% 5.68/5.85      ((((k2_tops_1 @ sk_A @ sk_B)
% 5.68/5.85          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 5.68/5.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.68/5.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.68/5.85                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 5.68/5.85      inference('sup+', [status(thm)], ['57', '58'])).
% 5.68/5.85  thf('60', plain,
% 5.68/5.85      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 5.68/5.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.68/5.85  thf(t44_xboole_1, axiom,
% 5.68/5.85    (![A:$i,B:$i,C:$i]:
% 5.68/5.85     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 5.68/5.85       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 5.68/5.85  thf('61', plain,
% 5.68/5.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.68/5.85         ((r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 5.68/5.85          | ~ (r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24))),
% 5.68/5.85      inference('cnf', [status(esa)], [t44_xboole_1])).
% 5.68/5.85  thf('62', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['60', '61'])).
% 5.68/5.85  thf(t3_subset, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.68/5.85  thf('63', plain,
% 5.68/5.85      (![X52 : $i, X54 : $i]:
% 5.68/5.85         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 5.68/5.85      inference('cnf', [status(esa)], [t3_subset])).
% 5.68/5.85  thf('64', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['62', '63'])).
% 5.68/5.85  thf(t40_xboole_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 5.68/5.85  thf('65', plain,
% 5.68/5.85      (![X20 : $i, X21 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 5.68/5.85           = (k4_xboole_0 @ X20 @ X21))),
% 5.68/5.85      inference('cnf', [status(esa)], [t40_xboole_1])).
% 5.68/5.85  thf('66', plain,
% 5.68/5.85      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 5.68/5.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.68/5.85  thf('67', plain,
% 5.68/5.85      (![X52 : $i, X54 : $i]:
% 5.68/5.85         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 5.68/5.85      inference('cnf', [status(esa)], [t3_subset])).
% 5.68/5.85  thf('68', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['66', '67'])).
% 5.68/5.85  thf('69', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (m1_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ 
% 5.68/5.85          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.68/5.85      inference('sup+', [status(thm)], ['65', '68'])).
% 5.68/5.85  thf(t32_subset_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.68/5.85       ( ![C:$i]:
% 5.68/5.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.68/5.85           ( ( k7_subset_1 @ A @ B @ C ) =
% 5.68/5.85             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 5.68/5.85  thf('70', plain,
% 5.68/5.85      (![X46 : $i, X47 : $i, X48 : $i]:
% 5.68/5.85         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 5.68/5.85          | ((k7_subset_1 @ X47 @ X48 @ X46)
% 5.68/5.85              = (k9_subset_1 @ X47 @ X48 @ (k3_subset_1 @ X47 @ X46)))
% 5.68/5.85          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X47)))),
% 5.68/5.85      inference('cnf', [status(esa)], [t32_subset_1])).
% 5.68/5.85  thf('71', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.68/5.85         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 5.68/5.85          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 5.68/5.85              (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 5.68/5.85                 (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 5.68/5.85                  (k4_xboole_0 @ X1 @ X0)))))),
% 5.68/5.85      inference('sup-', [status(thm)], ['69', '70'])).
% 5.68/5.85  thf('72', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['62', '63'])).
% 5.68/5.85  thf(involutiveness_k3_subset_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.68/5.85       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 5.68/5.85  thf('73', plain,
% 5.68/5.85      (![X38 : $i, X39 : $i]:
% 5.68/5.85         (((k3_subset_1 @ X39 @ (k3_subset_1 @ X39 @ X38)) = (X38))
% 5.68/5.85          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 5.68/5.85      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 5.68/5.85  thf('74', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 5.68/5.85           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['72', '73'])).
% 5.68/5.85  thf('75', plain,
% 5.68/5.85      (![X20 : $i, X21 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 5.68/5.85           = (k4_xboole_0 @ X20 @ X21))),
% 5.68/5.85      inference('cnf', [status(esa)], [t40_xboole_1])).
% 5.68/5.85  thf(t48_xboole_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.68/5.85  thf('76', plain,
% 5.68/5.85      (![X25 : $i, X26 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 5.68/5.85           = (k3_xboole_0 @ X25 @ X26))),
% 5.68/5.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.68/5.85  thf('77', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 5.68/5.85      inference('sup+', [status(thm)], ['75', '76'])).
% 5.68/5.85  thf(commutativity_k3_xboole_0, axiom,
% 5.68/5.85    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.68/5.85  thf('78', plain,
% 5.68/5.85      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 5.68/5.85      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.68/5.85  thf('79', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.68/5.85      inference('demod', [status(thm)], ['77', '78'])).
% 5.68/5.85  thf('80', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['60', '61'])).
% 5.68/5.85  thf(t28_xboole_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.68/5.85  thf('81', plain,
% 5.68/5.85      (![X16 : $i, X17 : $i]:
% 5.68/5.85         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 5.68/5.85      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.68/5.85  thf('82', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['80', '81'])).
% 5.68/5.85  thf('83', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85           = (X0))),
% 5.68/5.85      inference('demod', [status(thm)], ['79', '82'])).
% 5.68/5.85  thf('84', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['66', '67'])).
% 5.68/5.85  thf(d5_subset_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.68/5.85       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.68/5.85  thf('85', plain,
% 5.68/5.85      (![X28 : $i, X29 : $i]:
% 5.68/5.85         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 5.68/5.85          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 5.68/5.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.68/5.85  thf('86', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 5.68/5.85           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['84', '85'])).
% 5.68/5.85  thf('87', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 5.68/5.85           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))
% 5.68/5.85           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 5.68/5.85      inference('sup+', [status(thm)], ['83', '86'])).
% 5.68/5.85  thf('88', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85           = (X0))),
% 5.68/5.85      inference('demod', [status(thm)], ['79', '82'])).
% 5.68/5.85  thf('89', plain,
% 5.68/5.85      (![X20 : $i, X21 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 5.68/5.85           = (k4_xboole_0 @ X20 @ X21))),
% 5.68/5.85      inference('cnf', [status(esa)], [t40_xboole_1])).
% 5.68/5.85  thf('90', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 5.68/5.85           = (k4_xboole_0 @ X1 @ X0))),
% 5.68/5.85      inference('demod', [status(thm)], ['87', '88', '89'])).
% 5.68/5.85  thf('91', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85           = (X0))),
% 5.68/5.85      inference('demod', [status(thm)], ['74', '90'])).
% 5.68/5.85  thf('92', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.68/5.85         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 5.68/5.85          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 5.68/5.85              (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X0)))),
% 5.68/5.85      inference('demod', [status(thm)], ['71', '91'])).
% 5.68/5.85  thf('93', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 5.68/5.85           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['64', '92'])).
% 5.68/5.85  thf('94', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.68/5.85      inference('sup-', [status(thm)], ['62', '63'])).
% 5.68/5.85  thf('95', plain,
% 5.68/5.85      (![X43 : $i, X44 : $i, X45 : $i]:
% 5.68/5.85         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 5.68/5.85          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 5.68/5.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 5.68/5.85  thf('96', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.68/5.85         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X2)
% 5.68/5.85           = (k4_xboole_0 @ X0 @ X2))),
% 5.68/5.85      inference('sup-', [status(thm)], ['94', '95'])).
% 5.68/5.85  thf('97', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 5.68/5.85      inference('simplify', [status(thm)], ['12'])).
% 5.68/5.85  thf('98', plain,
% 5.68/5.85      (![X52 : $i, X54 : $i]:
% 5.68/5.85         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 5.68/5.85      inference('cnf', [status(esa)], [t3_subset])).
% 5.68/5.85  thf('99', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 5.68/5.85      inference('sup-', [status(thm)], ['97', '98'])).
% 5.68/5.85  thf(idempotence_k9_subset_1, axiom,
% 5.68/5.85    (![A:$i,B:$i,C:$i]:
% 5.68/5.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.68/5.85       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 5.68/5.85  thf('100', plain,
% 5.68/5.85      (![X35 : $i, X36 : $i, X37 : $i]:
% 5.68/5.85         (((k9_subset_1 @ X36 @ X35 @ X35) = (X35))
% 5.68/5.85          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 5.68/5.85      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 5.68/5.85  thf('101', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 5.68/5.85      inference('sup-', [status(thm)], ['99', '100'])).
% 5.68/5.85  thf('102', plain,
% 5.68/5.85      (![X0 : $i, X1 : $i]:
% 5.68/5.85         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 5.68/5.85      inference('demod', [status(thm)], ['93', '96', '101'])).
% 5.68/5.85  thf('103', plain,
% 5.68/5.85      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 5.68/5.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.68/5.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.68/5.85                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 5.68/5.85      inference('sup+', [status(thm)], ['59', '102'])).
% 5.68/5.85  thf('104', plain,
% 5.68/5.85      (((k1_tops_1 @ sk_A @ sk_B)
% 5.68/5.85         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 5.68/5.85      inference('demod', [status(thm)], ['19', '22'])).
% 5.68/5.85  thf('105', plain,
% 5.68/5.85      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 5.68/5.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.68/5.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.68/5.85                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 5.68/5.85      inference('sup+', [status(thm)], ['103', '104'])).
% 5.68/5.85  thf('106', plain,
% 5.68/5.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf(fc9_tops_1, axiom,
% 5.68/5.85    (![A:$i,B:$i]:
% 5.68/5.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 5.68/5.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.68/5.85       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 5.68/5.85  thf('107', plain,
% 5.68/5.85      (![X60 : $i, X61 : $i]:
% 5.68/5.85         (~ (l1_pre_topc @ X60)
% 5.68/5.85          | ~ (v2_pre_topc @ X60)
% 5.68/5.85          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 5.68/5.85          | (v3_pre_topc @ (k1_tops_1 @ X60 @ X61) @ X60))),
% 5.68/5.85      inference('cnf', [status(esa)], [fc9_tops_1])).
% 5.68/5.85  thf('108', plain,
% 5.68/5.85      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 5.68/5.85        | ~ (v2_pre_topc @ sk_A)
% 5.68/5.85        | ~ (l1_pre_topc @ sk_A))),
% 5.68/5.85      inference('sup-', [status(thm)], ['106', '107'])).
% 5.68/5.85  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 5.68/5.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.68/5.85  thf('111', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 5.68/5.85      inference('demod', [status(thm)], ['108', '109', '110'])).
% 5.68/5.85  thf('112', plain,
% 5.68/5.85      (((v3_pre_topc @ sk_B @ sk_A))
% 5.68/5.85         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 5.68/5.85                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.68/5.85                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 5.68/5.85      inference('sup+', [status(thm)], ['105', '111'])).
% 5.68/5.85  thf('113', plain,
% 5.68/5.85      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 5.68/5.85      inference('split', [status(esa)], ['0'])).
% 5.68/5.85  thf('114', plain,
% 5.68/5.85      (~
% 5.68/5.85       (((k2_tops_1 @ sk_A @ sk_B)
% 5.68/5.85          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.68/5.85             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 5.68/5.85       ((v3_pre_topc @ sk_B @ sk_A))),
% 5.68/5.85      inference('sup-', [status(thm)], ['112', '113'])).
% 5.68/5.85  thf('115', plain, ($false),
% 5.68/5.85      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '114'])).
% 5.68/5.85  
% 5.68/5.85  % SZS output end Refutation
% 5.68/5.85  
% 5.68/5.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
