%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WYUNbdVsXU

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:28 EST 2020

% Result     : Theorem 28.71s
% Output     : Refutation 28.71s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 369 expanded)
%              Number of leaves         :   45 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          : 1611 (3955 expanded)
%              Number of equality atoms :  104 ( 247 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X71: $i,X72: $i,X73: $i] :
      ( ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) )
      | ~ ( v3_pre_topc @ X71 @ X72 )
      | ~ ( r1_tarski @ X71 @ X73 )
      | ( r1_tarski @ X71 @ ( k1_tops_1 @ X72 @ X73 ) )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) )
      | ~ ( l1_pre_topc @ X72 ) ) ),
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
    ! [X78: $i,X79: $i] :
      ( ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X79 ) ) )
      | ( ( k1_tops_1 @ X79 @ X78 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X79 ) @ X78 @ ( k2_tops_1 @ X79 @ X78 ) ) )
      | ~ ( l1_pre_topc @ X79 ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k4_xboole_0 @ X47 @ X49 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
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
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ( ( k2_tops_1 @ X70 @ X69 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X70 ) @ ( k2_pre_topc @ X70 @ X69 ) @ ( k1_tops_1 @ X70 @ X69 ) ) )
      | ~ ( l1_pre_topc @ X70 ) ) ),
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
    ! [X65: $i,X66: $i] :
      ( ~ ( l1_pre_topc @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X65 @ X66 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X37 @ X36 @ X38 ) @ ( k1_zfmisc_1 @ X37 ) ) ) ),
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
    ! [X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X77 ) ) )
      | ( ( k2_pre_topc @ X77 @ X76 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X77 ) @ X76 @ ( k2_tops_1 @ X77 @ X76 ) ) )
      | ~ ( l1_pre_topc @ X77 ) ) ),
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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k4_xboole_0 @ X47 @ X49 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('61',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('68',plain,(
    ! [X59: $i,X61: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X61 ) )
      | ~ ( r1_tarski @ X59 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('71',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('72',plain,(
    ! [X59: $i,X61: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X61 ) )
      | ~ ( r1_tarski @ X59 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('75',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) )
      | ( ( k7_subset_1 @ X54 @ X55 @ X53 )
        = ( k9_subset_1 @ X54 @ X55 @ ( k3_subset_1 @ X54 @ X53 ) ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('78',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k3_subset_1 @ X43 @ ( k3_subset_1 @ X43 @ X42 ) )
        = X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('81',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('83',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('86',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('88',plain,(
    ! [X56: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('89',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r1_tarski @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('91',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('93',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('100',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['84','97'])).

thf('104',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['79','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('108',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k9_subset_1 @ X52 @ X50 @ X51 )
        = ( k3_xboole_0 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X0 )
      = ( k3_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('113',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k4_xboole_0 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X2 )
      = ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('116',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['111','114','117'])).

thf('119',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','118'])).

thf('120',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('121',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('123',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( l1_pre_topc @ X67 )
      | ~ ( v2_pre_topc @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X67 @ X68 ) @ X67 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('124',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['121','127'])).

thf('129',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('130',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WYUNbdVsXU
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 28.71/28.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 28.71/28.89  % Solved by: fo/fo7.sh
% 28.71/28.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.71/28.89  % done 21394 iterations in 28.440s
% 28.71/28.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 28.71/28.89  % SZS output start Refutation
% 28.71/28.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 28.71/28.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 28.71/28.89  thf(sk_B_type, type, sk_B: $i).
% 28.71/28.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 28.71/28.89  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 28.71/28.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 28.71/28.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 28.71/28.89  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 28.71/28.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 28.71/28.89  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 28.71/28.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 28.71/28.89  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 28.71/28.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 28.71/28.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 28.71/28.89  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 28.71/28.89  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 28.71/28.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 28.71/28.89  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 28.71/28.89  thf(sk_A_type, type, sk_A: $i).
% 28.71/28.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.71/28.89  thf(t76_tops_1, conjecture,
% 28.71/28.89    (![A:$i]:
% 28.71/28.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 28.71/28.89       ( ![B:$i]:
% 28.71/28.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 28.71/28.89           ( ( v3_pre_topc @ B @ A ) <=>
% 28.71/28.89             ( ( k2_tops_1 @ A @ B ) =
% 28.71/28.89               ( k7_subset_1 @
% 28.71/28.89                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 28.71/28.89  thf(zf_stmt_0, negated_conjecture,
% 28.71/28.89    (~( ![A:$i]:
% 28.71/28.89        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 28.71/28.89          ( ![B:$i]:
% 28.71/28.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 28.71/28.89              ( ( v3_pre_topc @ B @ A ) <=>
% 28.71/28.89                ( ( k2_tops_1 @ A @ B ) =
% 28.71/28.89                  ( k7_subset_1 @
% 28.71/28.89                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 28.71/28.89    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 28.71/28.89  thf('0', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 28.71/28.89        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('1', plain,
% 28.71/28.89      (~
% 28.71/28.89       (((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 28.71/28.89       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 28.71/28.89      inference('split', [status(esa)], ['0'])).
% 28.71/28.89  thf('2', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('3', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 28.71/28.89        | (v3_pre_topc @ sk_B @ sk_A))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('4', plain,
% 28.71/28.89      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 28.71/28.89      inference('split', [status(esa)], ['3'])).
% 28.71/28.89  thf('5', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf(t56_tops_1, axiom,
% 28.71/28.89    (![A:$i]:
% 28.71/28.89     ( ( l1_pre_topc @ A ) =>
% 28.71/28.89       ( ![B:$i]:
% 28.71/28.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 28.71/28.89           ( ![C:$i]:
% 28.71/28.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 28.71/28.89               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 28.71/28.89                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 28.71/28.89  thf('6', plain,
% 28.71/28.89      (![X71 : $i, X72 : $i, X73 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 28.71/28.89          | ~ (v3_pre_topc @ X71 @ X72)
% 28.71/28.89          | ~ (r1_tarski @ X71 @ X73)
% 28.71/28.89          | (r1_tarski @ X71 @ (k1_tops_1 @ X72 @ X73))
% 28.71/28.89          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 28.71/28.89          | ~ (l1_pre_topc @ X72))),
% 28.71/28.89      inference('cnf', [status(esa)], [t56_tops_1])).
% 28.71/28.89  thf('7', plain,
% 28.71/28.89      (![X0 : $i]:
% 28.71/28.89         (~ (l1_pre_topc @ sk_A)
% 28.71/28.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 28.71/28.89          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 28.71/28.89          | ~ (r1_tarski @ sk_B @ X0)
% 28.71/28.89          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 28.71/28.89      inference('sup-', [status(thm)], ['5', '6'])).
% 28.71/28.89  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('9', plain,
% 28.71/28.89      (![X0 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 28.71/28.89          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 28.71/28.89          | ~ (r1_tarski @ sk_B @ X0)
% 28.71/28.89          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 28.71/28.89      inference('demod', [status(thm)], ['7', '8'])).
% 28.71/28.89  thf('10', plain,
% 28.71/28.89      ((![X0 : $i]:
% 28.71/28.89          (~ (r1_tarski @ sk_B @ X0)
% 28.71/28.89           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 28.71/28.89           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 28.71/28.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['4', '9'])).
% 28.71/28.89  thf('11', plain,
% 28.71/28.89      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 28.71/28.89         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['2', '10'])).
% 28.71/28.89  thf(d10_xboole_0, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 28.71/28.89  thf('12', plain,
% 28.71/28.89      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 28.71/28.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 28.71/28.89  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 28.71/28.89      inference('simplify', [status(thm)], ['12'])).
% 28.71/28.89  thf('14', plain,
% 28.71/28.89      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 28.71/28.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 28.71/28.89      inference('demod', [status(thm)], ['11', '13'])).
% 28.71/28.89  thf('15', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf(t74_tops_1, axiom,
% 28.71/28.89    (![A:$i]:
% 28.71/28.89     ( ( l1_pre_topc @ A ) =>
% 28.71/28.89       ( ![B:$i]:
% 28.71/28.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 28.71/28.89           ( ( k1_tops_1 @ A @ B ) =
% 28.71/28.89             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 28.71/28.89  thf('16', plain,
% 28.71/28.89      (![X78 : $i, X79 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (u1_struct_0 @ X79)))
% 28.71/28.89          | ((k1_tops_1 @ X79 @ X78)
% 28.71/28.89              = (k7_subset_1 @ (u1_struct_0 @ X79) @ X78 @ 
% 28.71/28.89                 (k2_tops_1 @ X79 @ X78)))
% 28.71/28.89          | ~ (l1_pre_topc @ X79))),
% 28.71/28.89      inference('cnf', [status(esa)], [t74_tops_1])).
% 28.71/28.89  thf('17', plain,
% 28.71/28.89      ((~ (l1_pre_topc @ sk_A)
% 28.71/28.89        | ((k1_tops_1 @ sk_A @ sk_B)
% 28.71/28.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 28.71/28.89               (k2_tops_1 @ sk_A @ sk_B))))),
% 28.71/28.89      inference('sup-', [status(thm)], ['15', '16'])).
% 28.71/28.89  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('19', plain,
% 28.71/28.89      (((k1_tops_1 @ sk_A @ sk_B)
% 28.71/28.89         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 28.71/28.89            (k2_tops_1 @ sk_A @ sk_B)))),
% 28.71/28.89      inference('demod', [status(thm)], ['17', '18'])).
% 28.71/28.89  thf('20', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf(redefinition_k7_subset_1, axiom,
% 28.71/28.89    (![A:$i,B:$i,C:$i]:
% 28.71/28.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 28.71/28.89       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 28.71/28.89  thf('21', plain,
% 28.71/28.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 28.71/28.89          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k4_xboole_0 @ X47 @ X49)))),
% 28.71/28.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 28.71/28.89  thf('22', plain,
% 28.71/28.89      (![X0 : $i]:
% 28.71/28.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 28.71/28.89           = (k4_xboole_0 @ sk_B @ X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['20', '21'])).
% 28.71/28.89  thf('23', plain,
% 28.71/28.89      (((k1_tops_1 @ sk_A @ sk_B)
% 28.71/28.89         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 28.71/28.89      inference('demod', [status(thm)], ['19', '22'])).
% 28.71/28.89  thf(t36_xboole_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 28.71/28.89  thf('24', plain,
% 28.71/28.89      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 28.71/28.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 28.71/28.89  thf('25', plain,
% 28.71/28.89      (![X4 : $i, X6 : $i]:
% 28.71/28.89         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 28.71/28.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 28.71/28.89  thf('26', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 28.71/28.89          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['24', '25'])).
% 28.71/28.89  thf('27', plain,
% 28.71/28.89      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 28.71/28.89        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 28.71/28.89      inference('sup-', [status(thm)], ['23', '26'])).
% 28.71/28.89  thf('28', plain,
% 28.71/28.89      (((k1_tops_1 @ sk_A @ sk_B)
% 28.71/28.89         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 28.71/28.89      inference('demod', [status(thm)], ['19', '22'])).
% 28.71/28.89  thf('29', plain,
% 28.71/28.89      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 28.71/28.89        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 28.71/28.89      inference('demod', [status(thm)], ['27', '28'])).
% 28.71/28.89  thf('30', plain,
% 28.71/28.89      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 28.71/28.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['14', '29'])).
% 28.71/28.89  thf('31', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf(l78_tops_1, axiom,
% 28.71/28.89    (![A:$i]:
% 28.71/28.89     ( ( l1_pre_topc @ A ) =>
% 28.71/28.89       ( ![B:$i]:
% 28.71/28.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 28.71/28.89           ( ( k2_tops_1 @ A @ B ) =
% 28.71/28.89             ( k7_subset_1 @
% 28.71/28.89               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 28.71/28.89               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 28.71/28.89  thf('32', plain,
% 28.71/28.89      (![X69 : $i, X70 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 28.71/28.89          | ((k2_tops_1 @ X70 @ X69)
% 28.71/28.89              = (k7_subset_1 @ (u1_struct_0 @ X70) @ 
% 28.71/28.89                 (k2_pre_topc @ X70 @ X69) @ (k1_tops_1 @ X70 @ X69)))
% 28.71/28.89          | ~ (l1_pre_topc @ X70))),
% 28.71/28.89      inference('cnf', [status(esa)], [l78_tops_1])).
% 28.71/28.89  thf('33', plain,
% 28.71/28.89      ((~ (l1_pre_topc @ sk_A)
% 28.71/28.89        | ((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 28.71/28.89      inference('sup-', [status(thm)], ['31', '32'])).
% 28.71/28.89  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('35', plain,
% 28.71/28.89      (((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 28.71/28.89            (k1_tops_1 @ sk_A @ sk_B)))),
% 28.71/28.89      inference('demod', [status(thm)], ['33', '34'])).
% 28.71/28.89  thf('36', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 28.71/28.89         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 28.71/28.89      inference('sup+', [status(thm)], ['30', '35'])).
% 28.71/28.89  thf('37', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 28.71/28.89         <= (~
% 28.71/28.89             (((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 28.71/28.89      inference('split', [status(esa)], ['0'])).
% 28.71/28.89  thf('38', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 28.71/28.89         <= (~
% 28.71/28.89             (((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 28.71/28.89             ((v3_pre_topc @ sk_B @ sk_A)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['36', '37'])).
% 28.71/28.89  thf('39', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 28.71/28.89       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 28.71/28.89      inference('simplify', [status(thm)], ['38'])).
% 28.71/28.89  thf('40', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 28.71/28.89       ((v3_pre_topc @ sk_B @ sk_A))),
% 28.71/28.89      inference('split', [status(esa)], ['3'])).
% 28.71/28.89  thf('41', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf(dt_k2_tops_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( ( l1_pre_topc @ A ) & 
% 28.71/28.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 28.71/28.89       ( m1_subset_1 @
% 28.71/28.89         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 28.71/28.89  thf('42', plain,
% 28.71/28.89      (![X65 : $i, X66 : $i]:
% 28.71/28.89         (~ (l1_pre_topc @ X65)
% 28.71/28.89          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 28.71/28.89          | (m1_subset_1 @ (k2_tops_1 @ X65 @ X66) @ 
% 28.71/28.89             (k1_zfmisc_1 @ (u1_struct_0 @ X65))))),
% 28.71/28.89      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 28.71/28.89  thf('43', plain,
% 28.71/28.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 28.71/28.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 28.71/28.89        | ~ (l1_pre_topc @ sk_A))),
% 28.71/28.89      inference('sup-', [status(thm)], ['41', '42'])).
% 28.71/28.89  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('45', plain,
% 28.71/28.89      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 28.71/28.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('demod', [status(thm)], ['43', '44'])).
% 28.71/28.89  thf('46', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf(dt_k4_subset_1, axiom,
% 28.71/28.89    (![A:$i,B:$i,C:$i]:
% 28.71/28.89     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 28.71/28.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 28.71/28.89       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 28.71/28.89  thf('47', plain,
% 28.71/28.89      (![X36 : $i, X37 : $i, X38 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 28.71/28.89          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 28.71/28.89          | (m1_subset_1 @ (k4_subset_1 @ X37 @ X36 @ X38) @ 
% 28.71/28.89             (k1_zfmisc_1 @ X37)))),
% 28.71/28.89      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 28.71/28.89  thf('48', plain,
% 28.71/28.89      (![X0 : $i]:
% 28.71/28.89         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 28.71/28.89           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 28.71/28.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 28.71/28.89      inference('sup-', [status(thm)], ['46', '47'])).
% 28.71/28.89  thf('49', plain,
% 28.71/28.89      ((m1_subset_1 @ 
% 28.71/28.89        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 28.71/28.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['45', '48'])).
% 28.71/28.89  thf('50', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf(t65_tops_1, axiom,
% 28.71/28.89    (![A:$i]:
% 28.71/28.89     ( ( l1_pre_topc @ A ) =>
% 28.71/28.89       ( ![B:$i]:
% 28.71/28.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 28.71/28.89           ( ( k2_pre_topc @ A @ B ) =
% 28.71/28.89             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 28.71/28.89  thf('51', plain,
% 28.71/28.89      (![X76 : $i, X77 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (u1_struct_0 @ X77)))
% 28.71/28.89          | ((k2_pre_topc @ X77 @ X76)
% 28.71/28.89              = (k4_subset_1 @ (u1_struct_0 @ X77) @ X76 @ 
% 28.71/28.89                 (k2_tops_1 @ X77 @ X76)))
% 28.71/28.89          | ~ (l1_pre_topc @ X77))),
% 28.71/28.89      inference('cnf', [status(esa)], [t65_tops_1])).
% 28.71/28.89  thf('52', plain,
% 28.71/28.89      ((~ (l1_pre_topc @ sk_A)
% 28.71/28.89        | ((k2_pre_topc @ sk_A @ sk_B)
% 28.71/28.89            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 28.71/28.89               (k2_tops_1 @ sk_A @ sk_B))))),
% 28.71/28.89      inference('sup-', [status(thm)], ['50', '51'])).
% 28.71/28.89  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('54', plain,
% 28.71/28.89      (((k2_pre_topc @ sk_A @ sk_B)
% 28.71/28.89         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 28.71/28.89            (k2_tops_1 @ sk_A @ sk_B)))),
% 28.71/28.89      inference('demod', [status(thm)], ['52', '53'])).
% 28.71/28.89  thf('55', plain,
% 28.71/28.89      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 28.71/28.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('demod', [status(thm)], ['49', '54'])).
% 28.71/28.89  thf('56', plain,
% 28.71/28.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 28.71/28.89          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k4_xboole_0 @ X47 @ X49)))),
% 28.71/28.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 28.71/28.89  thf('57', plain,
% 28.71/28.89      (![X0 : $i]:
% 28.71/28.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 28.71/28.89           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['55', '56'])).
% 28.71/28.89  thf('58', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 28.71/28.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 28.71/28.89      inference('split', [status(esa)], ['3'])).
% 28.71/28.89  thf('59', plain,
% 28.71/28.89      ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 28.71/28.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 28.71/28.89      inference('sup+', [status(thm)], ['57', '58'])).
% 28.71/28.89  thf('60', plain,
% 28.71/28.89      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 28.71/28.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 28.71/28.89  thf(l32_xboole_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 28.71/28.89  thf('61', plain,
% 28.71/28.89      (![X7 : $i, X9 : $i]:
% 28.71/28.89         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 28.71/28.89      inference('cnf', [status(esa)], [l32_xboole_1])).
% 28.71/28.89  thf('62', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['60', '61'])).
% 28.71/28.89  thf(t41_xboole_1, axiom,
% 28.71/28.89    (![A:$i,B:$i,C:$i]:
% 28.71/28.89     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 28.71/28.89       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 28.71/28.89  thf('63', plain,
% 28.71/28.89      (![X25 : $i, X26 : $i, X27 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 28.71/28.89           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 28.71/28.89      inference('cnf', [status(esa)], [t41_xboole_1])).
% 28.71/28.89  thf('64', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 28.71/28.89      inference('demod', [status(thm)], ['62', '63'])).
% 28.71/28.89  thf('65', plain,
% 28.71/28.89      (![X7 : $i, X8 : $i]:
% 28.71/28.89         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 28.71/28.89      inference('cnf', [status(esa)], [l32_xboole_1])).
% 28.71/28.89  thf('66', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (((k1_xboole_0) != (k1_xboole_0))
% 28.71/28.89          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['64', '65'])).
% 28.71/28.89  thf('67', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 28.71/28.89      inference('simplify', [status(thm)], ['66'])).
% 28.71/28.89  thf(t3_subset, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 28.71/28.89  thf('68', plain,
% 28.71/28.89      (![X59 : $i, X61 : $i]:
% 28.71/28.89         ((m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X61)) | ~ (r1_tarski @ X59 @ X61))),
% 28.71/28.89      inference('cnf', [status(esa)], [t3_subset])).
% 28.71/28.89  thf('69', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['67', '68'])).
% 28.71/28.89  thf(t40_xboole_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 28.71/28.89  thf('70', plain,
% 28.71/28.89      (![X23 : $i, X24 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 28.71/28.89           = (k4_xboole_0 @ X23 @ X24))),
% 28.71/28.89      inference('cnf', [status(esa)], [t40_xboole_1])).
% 28.71/28.89  thf('71', plain,
% 28.71/28.89      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 28.71/28.89      inference('cnf', [status(esa)], [t36_xboole_1])).
% 28.71/28.89  thf('72', plain,
% 28.71/28.89      (![X59 : $i, X61 : $i]:
% 28.71/28.89         ((m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X61)) | ~ (r1_tarski @ X59 @ X61))),
% 28.71/28.89      inference('cnf', [status(esa)], [t3_subset])).
% 28.71/28.89  thf('73', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['71', '72'])).
% 28.71/28.89  thf('74', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (m1_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ 
% 28.71/28.89          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('sup+', [status(thm)], ['70', '73'])).
% 28.71/28.89  thf(t32_subset_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 28.71/28.89       ( ![C:$i]:
% 28.71/28.89         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 28.71/28.89           ( ( k7_subset_1 @ A @ B @ C ) =
% 28.71/28.89             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 28.71/28.89  thf('75', plain,
% 28.71/28.89      (![X53 : $i, X54 : $i, X55 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54))
% 28.71/28.89          | ((k7_subset_1 @ X54 @ X55 @ X53)
% 28.71/28.89              = (k9_subset_1 @ X54 @ X55 @ (k3_subset_1 @ X54 @ X53)))
% 28.71/28.89          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X54)))),
% 28.71/28.89      inference('cnf', [status(esa)], [t32_subset_1])).
% 28.71/28.89  thf('76', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 28.71/28.89          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 28.71/28.89              (k4_xboole_0 @ X1 @ X0))
% 28.71/28.89              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 28.71/28.89                 (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 28.71/28.89                  (k4_xboole_0 @ X1 @ X0)))))),
% 28.71/28.89      inference('sup-', [status(thm)], ['74', '75'])).
% 28.71/28.89  thf('77', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['67', '68'])).
% 28.71/28.89  thf(involutiveness_k3_subset_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 28.71/28.89       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 28.71/28.89  thf('78', plain,
% 28.71/28.89      (![X42 : $i, X43 : $i]:
% 28.71/28.89         (((k3_subset_1 @ X43 @ (k3_subset_1 @ X43 @ X42)) = (X42))
% 28.71/28.89          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 28.71/28.89      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 28.71/28.89  thf('79', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 28.71/28.89           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['77', '78'])).
% 28.71/28.89  thf('80', plain,
% 28.71/28.89      (![X23 : $i, X24 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 28.71/28.89           = (k4_xboole_0 @ X23 @ X24))),
% 28.71/28.89      inference('cnf', [status(esa)], [t40_xboole_1])).
% 28.71/28.89  thf(t48_xboole_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 28.71/28.89  thf('81', plain,
% 28.71/28.89      (![X28 : $i, X29 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 28.71/28.89           = (k3_xboole_0 @ X28 @ X29))),
% 28.71/28.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 28.71/28.89  thf('82', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 28.71/28.89           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 28.71/28.89      inference('sup+', [status(thm)], ['80', '81'])).
% 28.71/28.89  thf(commutativity_k3_xboole_0, axiom,
% 28.71/28.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 28.71/28.89  thf('83', plain,
% 28.71/28.89      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 28.71/28.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 28.71/28.89  thf('84', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 28.71/28.89           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('demod', [status(thm)], ['82', '83'])).
% 28.71/28.89  thf('85', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 28.71/28.89      inference('demod', [status(thm)], ['62', '63'])).
% 28.71/28.89  thf('86', plain,
% 28.71/28.89      (![X28 : $i, X29 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 28.71/28.89           = (k3_xboole_0 @ X28 @ X29))),
% 28.71/28.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 28.71/28.89  thf('87', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 28.71/28.89           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('sup+', [status(thm)], ['85', '86'])).
% 28.71/28.89  thf(t4_subset_1, axiom,
% 28.71/28.89    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 28.71/28.89  thf('88', plain,
% 28.71/28.89      (![X56 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X56))),
% 28.71/28.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 28.71/28.89  thf('89', plain,
% 28.71/28.89      (![X59 : $i, X60 : $i]:
% 28.71/28.89         ((r1_tarski @ X59 @ X60) | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ X60)))),
% 28.71/28.89      inference('cnf', [status(esa)], [t3_subset])).
% 28.71/28.89  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 28.71/28.89      inference('sup-', [status(thm)], ['88', '89'])).
% 28.71/28.89  thf(t12_xboole_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 28.71/28.89  thf('91', plain,
% 28.71/28.89      (![X12 : $i, X13 : $i]:
% 28.71/28.89         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 28.71/28.89      inference('cnf', [status(esa)], [t12_xboole_1])).
% 28.71/28.89  thf('92', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['90', '91'])).
% 28.71/28.89  thf(t39_xboole_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 28.71/28.89  thf('93', plain,
% 28.71/28.89      (![X21 : $i, X22 : $i]:
% 28.71/28.89         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 28.71/28.89           = (k2_xboole_0 @ X21 @ X22))),
% 28.71/28.89      inference('cnf', [status(esa)], [t39_xboole_1])).
% 28.71/28.89  thf('94', plain,
% 28.71/28.89      (![X0 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 28.71/28.89      inference('sup+', [status(thm)], ['92', '93'])).
% 28.71/28.89  thf('95', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['90', '91'])).
% 28.71/28.89  thf('96', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 28.71/28.89      inference('demod', [status(thm)], ['94', '95'])).
% 28.71/28.89  thf('97', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('demod', [status(thm)], ['87', '96'])).
% 28.71/28.89  thf('98', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 28.71/28.89           = (X0))),
% 28.71/28.89      inference('demod', [status(thm)], ['84', '97'])).
% 28.71/28.89  thf('99', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['71', '72'])).
% 28.71/28.89  thf(d5_subset_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 28.71/28.89       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 28.71/28.89  thf('100', plain,
% 28.71/28.89      (![X31 : $i, X32 : $i]:
% 28.71/28.89         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 28.71/28.89          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 28.71/28.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 28.71/28.89  thf('101', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 28.71/28.89           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['99', '100'])).
% 28.71/28.89  thf('102', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 28.71/28.89           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))
% 28.71/28.89           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 28.71/28.89      inference('sup+', [status(thm)], ['98', '101'])).
% 28.71/28.89  thf('103', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 28.71/28.89           = (X0))),
% 28.71/28.89      inference('demod', [status(thm)], ['84', '97'])).
% 28.71/28.89  thf('104', plain,
% 28.71/28.89      (![X23 : $i, X24 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 28.71/28.89           = (k4_xboole_0 @ X23 @ X24))),
% 28.71/28.89      inference('cnf', [status(esa)], [t40_xboole_1])).
% 28.71/28.89  thf('105', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 28.71/28.89           = (k4_xboole_0 @ X1 @ X0))),
% 28.71/28.89      inference('demod', [status(thm)], ['102', '103', '104'])).
% 28.71/28.89  thf('106', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 28.71/28.89           = (X0))),
% 28.71/28.89      inference('demod', [status(thm)], ['79', '105'])).
% 28.71/28.89  thf('107', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['67', '68'])).
% 28.71/28.89  thf(redefinition_k9_subset_1, axiom,
% 28.71/28.89    (![A:$i,B:$i,C:$i]:
% 28.71/28.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 28.71/28.89       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 28.71/28.89  thf('108', plain,
% 28.71/28.89      (![X50 : $i, X51 : $i, X52 : $i]:
% 28.71/28.89         (((k9_subset_1 @ X52 @ X50 @ X51) = (k3_xboole_0 @ X50 @ X51))
% 28.71/28.89          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52)))),
% 28.71/28.89      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 28.71/28.89  thf('109', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.71/28.89         ((k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X0)
% 28.71/28.89           = (k3_xboole_0 @ X2 @ X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['107', '108'])).
% 28.71/28.89  thf('110', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 28.71/28.89          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 28.71/28.89              (k4_xboole_0 @ X1 @ X0)) = (k3_xboole_0 @ X2 @ X0)))),
% 28.71/28.89      inference('demod', [status(thm)], ['76', '106', '109'])).
% 28.71/28.89  thf('111', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 28.71/28.89           = (k3_xboole_0 @ X0 @ X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['69', '110'])).
% 28.71/28.89  thf('112', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 28.71/28.89      inference('sup-', [status(thm)], ['67', '68'])).
% 28.71/28.89  thf('113', plain,
% 28.71/28.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 28.71/28.89         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 28.71/28.89          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k4_xboole_0 @ X47 @ X49)))),
% 28.71/28.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 28.71/28.89  thf('114', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.71/28.89         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X2)
% 28.71/28.89           = (k4_xboole_0 @ X0 @ X2))),
% 28.71/28.89      inference('sup-', [status(thm)], ['112', '113'])).
% 28.71/28.89  thf('115', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 28.71/28.89      inference('simplify', [status(thm)], ['12'])).
% 28.71/28.89  thf(t28_xboole_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 28.71/28.89  thf('116', plain,
% 28.71/28.89      (![X17 : $i, X18 : $i]:
% 28.71/28.89         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 28.71/28.89      inference('cnf', [status(esa)], [t28_xboole_1])).
% 28.71/28.89  thf('117', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 28.71/28.89      inference('sup-', [status(thm)], ['115', '116'])).
% 28.71/28.89  thf('118', plain,
% 28.71/28.89      (![X0 : $i, X1 : $i]:
% 28.71/28.89         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 28.71/28.89      inference('demod', [status(thm)], ['111', '114', '117'])).
% 28.71/28.89  thf('119', plain,
% 28.71/28.89      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 28.71/28.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 28.71/28.89      inference('sup+', [status(thm)], ['59', '118'])).
% 28.71/28.89  thf('120', plain,
% 28.71/28.89      (((k1_tops_1 @ sk_A @ sk_B)
% 28.71/28.89         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 28.71/28.89      inference('demod', [status(thm)], ['19', '22'])).
% 28.71/28.89  thf('121', plain,
% 28.71/28.89      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 28.71/28.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 28.71/28.89      inference('sup+', [status(thm)], ['119', '120'])).
% 28.71/28.89  thf('122', plain,
% 28.71/28.89      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf(fc9_tops_1, axiom,
% 28.71/28.89    (![A:$i,B:$i]:
% 28.71/28.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 28.71/28.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 28.71/28.89       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 28.71/28.89  thf('123', plain,
% 28.71/28.89      (![X67 : $i, X68 : $i]:
% 28.71/28.89         (~ (l1_pre_topc @ X67)
% 28.71/28.89          | ~ (v2_pre_topc @ X67)
% 28.71/28.89          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 28.71/28.89          | (v3_pre_topc @ (k1_tops_1 @ X67 @ X68) @ X67))),
% 28.71/28.89      inference('cnf', [status(esa)], [fc9_tops_1])).
% 28.71/28.89  thf('124', plain,
% 28.71/28.89      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 28.71/28.89        | ~ (v2_pre_topc @ sk_A)
% 28.71/28.89        | ~ (l1_pre_topc @ sk_A))),
% 28.71/28.89      inference('sup-', [status(thm)], ['122', '123'])).
% 28.71/28.89  thf('125', plain, ((v2_pre_topc @ sk_A)),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 28.71/28.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.71/28.89  thf('127', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 28.71/28.89      inference('demod', [status(thm)], ['124', '125', '126'])).
% 28.71/28.89  thf('128', plain,
% 28.71/28.89      (((v3_pre_topc @ sk_B @ sk_A))
% 28.71/28.89         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 28.71/28.89      inference('sup+', [status(thm)], ['121', '127'])).
% 28.71/28.89  thf('129', plain,
% 28.71/28.89      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 28.71/28.89      inference('split', [status(esa)], ['0'])).
% 28.71/28.89  thf('130', plain,
% 28.71/28.89      (~
% 28.71/28.89       (((k2_tops_1 @ sk_A @ sk_B)
% 28.71/28.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 28.71/28.89             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 28.71/28.89       ((v3_pre_topc @ sk_B @ sk_A))),
% 28.71/28.89      inference('sup-', [status(thm)], ['128', '129'])).
% 28.71/28.89  thf('131', plain, ($false),
% 28.71/28.89      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '130'])).
% 28.71/28.89  
% 28.71/28.89  % SZS output end Refutation
% 28.71/28.89  
% 28.71/28.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
