%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KoXQZHoGyY

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:28 EST 2020

% Result     : Theorem 20.29s
% Output     : Refutation 20.29s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 203 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          : 1097 (2653 expanded)
%              Number of equality atoms :   64 ( 141 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X73: $i,X74: $i,X75: $i] :
      ( ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X74 ) ) )
      | ~ ( v3_pre_topc @ X73 @ X74 )
      | ~ ( r1_tarski @ X73 @ X75 )
      | ( r1_tarski @ X73 @ ( k1_tops_1 @ X74 @ X75 ) )
      | ~ ( m1_subset_1 @ X75 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X74 ) ) )
      | ~ ( l1_pre_topc @ X74 ) ) ),
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
    ! [X80: $i,X81: $i] :
      ( ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X81 ) ) )
      | ( ( k1_tops_1 @ X81 @ X80 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X81 ) @ X80 @ ( k2_tops_1 @ X81 @ X80 ) ) )
      | ~ ( l1_pre_topc @ X81 ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( ( k7_subset_1 @ X50 @ X49 @ X51 )
        = ( k4_xboole_0 @ X49 @ X51 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
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
    ! [X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) )
      | ( ( k2_tops_1 @ X72 @ X71 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X72 ) @ ( k2_pre_topc @ X72 @ X71 ) @ ( k1_tops_1 @ X72 @ X71 ) ) )
      | ~ ( l1_pre_topc @ X72 ) ) ),
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
    ! [X67: $i,X68: $i] :
      ( ~ ( l1_pre_topc @ X67 )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X67 @ X68 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X36 @ X35 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ) ),
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
    ! [X78: $i,X79: $i] :
      ( ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X79 ) ) )
      | ( ( k2_pre_topc @ X79 @ X78 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X79 ) @ X78 @ ( k2_tops_1 @ X79 @ X78 ) ) )
      | ~ ( l1_pre_topc @ X79 ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( ( k7_subset_1 @ X50 @ X49 @ X51 )
        = ( k4_xboole_0 @ X49 @ X51 ) ) ) ),
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
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('61',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('63',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X28 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','72'])).

thf('74',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('75',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('77',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( l1_pre_topc @ X69 )
      | ~ ( v2_pre_topc @ X69 )
      | ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X69 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X69 @ X70 ) @ X69 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('78',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','81'])).

thf('83',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KoXQZHoGyY
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 20.29/20.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.29/20.47  % Solved by: fo/fo7.sh
% 20.29/20.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.29/20.47  % done 20834 iterations in 20.014s
% 20.29/20.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.29/20.47  % SZS output start Refutation
% 20.29/20.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 20.29/20.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 20.29/20.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.29/20.47  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 20.29/20.47  thf(sk_A_type, type, sk_A: $i).
% 20.29/20.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 20.29/20.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 20.29/20.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 20.29/20.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.29/20.47  thf(sk_B_type, type, sk_B: $i).
% 20.29/20.47  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 20.29/20.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.29/20.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 20.29/20.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 20.29/20.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 20.29/20.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 20.29/20.47  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 20.29/20.47  thf(t76_tops_1, conjecture,
% 20.29/20.47    (![A:$i]:
% 20.29/20.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.29/20.47       ( ![B:$i]:
% 20.29/20.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.29/20.47           ( ( v3_pre_topc @ B @ A ) <=>
% 20.29/20.47             ( ( k2_tops_1 @ A @ B ) =
% 20.29/20.47               ( k7_subset_1 @
% 20.29/20.47                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 20.29/20.47  thf(zf_stmt_0, negated_conjecture,
% 20.29/20.47    (~( ![A:$i]:
% 20.29/20.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.29/20.47          ( ![B:$i]:
% 20.29/20.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.29/20.47              ( ( v3_pre_topc @ B @ A ) <=>
% 20.29/20.47                ( ( k2_tops_1 @ A @ B ) =
% 20.29/20.47                  ( k7_subset_1 @
% 20.29/20.47                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 20.29/20.47    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 20.29/20.47  thf('0', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 20.29/20.47        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('1', plain,
% 20.29/20.47      (~
% 20.29/20.47       (((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 20.29/20.47       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 20.29/20.47      inference('split', [status(esa)], ['0'])).
% 20.29/20.47  thf('2', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('3', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 20.29/20.47        | (v3_pre_topc @ sk_B @ sk_A))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('4', plain,
% 20.29/20.47      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 20.29/20.47      inference('split', [status(esa)], ['3'])).
% 20.29/20.47  thf('5', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf(t56_tops_1, axiom,
% 20.29/20.47    (![A:$i]:
% 20.29/20.47     ( ( l1_pre_topc @ A ) =>
% 20.29/20.47       ( ![B:$i]:
% 20.29/20.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.29/20.47           ( ![C:$i]:
% 20.29/20.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.29/20.47               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 20.29/20.47                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 20.29/20.47  thf('6', plain,
% 20.29/20.47      (![X73 : $i, X74 : $i, X75 : $i]:
% 20.29/20.47         (~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (u1_struct_0 @ X74)))
% 20.29/20.47          | ~ (v3_pre_topc @ X73 @ X74)
% 20.29/20.47          | ~ (r1_tarski @ X73 @ X75)
% 20.29/20.47          | (r1_tarski @ X73 @ (k1_tops_1 @ X74 @ X75))
% 20.29/20.47          | ~ (m1_subset_1 @ X75 @ (k1_zfmisc_1 @ (u1_struct_0 @ X74)))
% 20.29/20.47          | ~ (l1_pre_topc @ X74))),
% 20.29/20.47      inference('cnf', [status(esa)], [t56_tops_1])).
% 20.29/20.47  thf('7', plain,
% 20.29/20.47      (![X0 : $i]:
% 20.29/20.47         (~ (l1_pre_topc @ sk_A)
% 20.29/20.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.29/20.47          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 20.29/20.47          | ~ (r1_tarski @ sk_B @ X0)
% 20.29/20.47          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 20.29/20.47      inference('sup-', [status(thm)], ['5', '6'])).
% 20.29/20.47  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('9', plain,
% 20.29/20.47      (![X0 : $i]:
% 20.29/20.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.29/20.47          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 20.29/20.47          | ~ (r1_tarski @ sk_B @ X0)
% 20.29/20.47          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 20.29/20.47      inference('demod', [status(thm)], ['7', '8'])).
% 20.29/20.47  thf('10', plain,
% 20.29/20.47      ((![X0 : $i]:
% 20.29/20.47          (~ (r1_tarski @ sk_B @ X0)
% 20.29/20.47           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 20.29/20.47           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 20.29/20.47         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 20.29/20.47      inference('sup-', [status(thm)], ['4', '9'])).
% 20.29/20.47  thf('11', plain,
% 20.29/20.47      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 20.29/20.47         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 20.29/20.47      inference('sup-', [status(thm)], ['2', '10'])).
% 20.29/20.47  thf(d10_xboole_0, axiom,
% 20.29/20.47    (![A:$i,B:$i]:
% 20.29/20.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 20.29/20.47  thf('12', plain,
% 20.29/20.47      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 20.29/20.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.29/20.47  thf('13', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 20.29/20.47      inference('simplify', [status(thm)], ['12'])).
% 20.29/20.47  thf('14', plain,
% 20.29/20.47      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 20.29/20.47         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 20.29/20.47      inference('demod', [status(thm)], ['11', '13'])).
% 20.29/20.47  thf('15', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf(t74_tops_1, axiom,
% 20.29/20.47    (![A:$i]:
% 20.29/20.47     ( ( l1_pre_topc @ A ) =>
% 20.29/20.47       ( ![B:$i]:
% 20.29/20.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.29/20.47           ( ( k1_tops_1 @ A @ B ) =
% 20.29/20.47             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 20.29/20.47  thf('16', plain,
% 20.29/20.47      (![X80 : $i, X81 : $i]:
% 20.29/20.47         (~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (u1_struct_0 @ X81)))
% 20.29/20.47          | ((k1_tops_1 @ X81 @ X80)
% 20.29/20.47              = (k7_subset_1 @ (u1_struct_0 @ X81) @ X80 @ 
% 20.29/20.47                 (k2_tops_1 @ X81 @ X80)))
% 20.29/20.47          | ~ (l1_pre_topc @ X81))),
% 20.29/20.47      inference('cnf', [status(esa)], [t74_tops_1])).
% 20.29/20.47  thf('17', plain,
% 20.29/20.47      ((~ (l1_pre_topc @ sk_A)
% 20.29/20.47        | ((k1_tops_1 @ sk_A @ sk_B)
% 20.29/20.47            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 20.29/20.47               (k2_tops_1 @ sk_A @ sk_B))))),
% 20.29/20.47      inference('sup-', [status(thm)], ['15', '16'])).
% 20.29/20.47  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('19', plain,
% 20.29/20.47      (((k1_tops_1 @ sk_A @ sk_B)
% 20.29/20.47         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 20.29/20.47            (k2_tops_1 @ sk_A @ sk_B)))),
% 20.29/20.47      inference('demod', [status(thm)], ['17', '18'])).
% 20.29/20.47  thf('20', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf(redefinition_k7_subset_1, axiom,
% 20.29/20.47    (![A:$i,B:$i,C:$i]:
% 20.29/20.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 20.29/20.47       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 20.29/20.47  thf('21', plain,
% 20.29/20.47      (![X49 : $i, X50 : $i, X51 : $i]:
% 20.29/20.47         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 20.29/20.47          | ((k7_subset_1 @ X50 @ X49 @ X51) = (k4_xboole_0 @ X49 @ X51)))),
% 20.29/20.47      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 20.29/20.47  thf('22', plain,
% 20.29/20.47      (![X0 : $i]:
% 20.29/20.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 20.29/20.47           = (k4_xboole_0 @ sk_B @ X0))),
% 20.29/20.47      inference('sup-', [status(thm)], ['20', '21'])).
% 20.29/20.47  thf('23', plain,
% 20.29/20.47      (((k1_tops_1 @ sk_A @ sk_B)
% 20.29/20.47         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 20.29/20.47      inference('demod', [status(thm)], ['19', '22'])).
% 20.29/20.47  thf(t36_xboole_1, axiom,
% 20.29/20.47    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 20.29/20.47  thf('24', plain,
% 20.29/20.47      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 20.29/20.47      inference('cnf', [status(esa)], [t36_xboole_1])).
% 20.29/20.47  thf('25', plain,
% 20.29/20.47      (![X4 : $i, X6 : $i]:
% 20.29/20.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 20.29/20.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.29/20.47  thf('26', plain,
% 20.29/20.47      (![X0 : $i, X1 : $i]:
% 20.29/20.47         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 20.29/20.47          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 20.29/20.47      inference('sup-', [status(thm)], ['24', '25'])).
% 20.29/20.47  thf('27', plain,
% 20.29/20.47      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 20.29/20.47        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 20.29/20.47      inference('sup-', [status(thm)], ['23', '26'])).
% 20.29/20.47  thf('28', plain,
% 20.29/20.47      (((k1_tops_1 @ sk_A @ sk_B)
% 20.29/20.47         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 20.29/20.47      inference('demod', [status(thm)], ['19', '22'])).
% 20.29/20.47  thf('29', plain,
% 20.29/20.47      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 20.29/20.47        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 20.29/20.47      inference('demod', [status(thm)], ['27', '28'])).
% 20.29/20.47  thf('30', plain,
% 20.29/20.47      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 20.29/20.47         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 20.29/20.47      inference('sup-', [status(thm)], ['14', '29'])).
% 20.29/20.47  thf('31', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf(l78_tops_1, axiom,
% 20.29/20.47    (![A:$i]:
% 20.29/20.47     ( ( l1_pre_topc @ A ) =>
% 20.29/20.47       ( ![B:$i]:
% 20.29/20.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.29/20.47           ( ( k2_tops_1 @ A @ B ) =
% 20.29/20.47             ( k7_subset_1 @
% 20.29/20.47               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 20.29/20.47               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 20.29/20.47  thf('32', plain,
% 20.29/20.47      (![X71 : $i, X72 : $i]:
% 20.29/20.47         (~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 20.29/20.47          | ((k2_tops_1 @ X72 @ X71)
% 20.29/20.47              = (k7_subset_1 @ (u1_struct_0 @ X72) @ 
% 20.29/20.47                 (k2_pre_topc @ X72 @ X71) @ (k1_tops_1 @ X72 @ X71)))
% 20.29/20.47          | ~ (l1_pre_topc @ X72))),
% 20.29/20.47      inference('cnf', [status(esa)], [l78_tops_1])).
% 20.29/20.47  thf('33', plain,
% 20.29/20.47      ((~ (l1_pre_topc @ sk_A)
% 20.29/20.47        | ((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 20.29/20.47      inference('sup-', [status(thm)], ['31', '32'])).
% 20.29/20.47  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('35', plain,
% 20.29/20.47      (((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 20.29/20.47            (k1_tops_1 @ sk_A @ sk_B)))),
% 20.29/20.47      inference('demod', [status(thm)], ['33', '34'])).
% 20.29/20.47  thf('36', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 20.29/20.47         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 20.29/20.47      inference('sup+', [status(thm)], ['30', '35'])).
% 20.29/20.47  thf('37', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 20.29/20.47         <= (~
% 20.29/20.47             (((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 20.29/20.47      inference('split', [status(esa)], ['0'])).
% 20.29/20.47  thf('38', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 20.29/20.47         <= (~
% 20.29/20.47             (((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 20.29/20.47             ((v3_pre_topc @ sk_B @ sk_A)))),
% 20.29/20.47      inference('sup-', [status(thm)], ['36', '37'])).
% 20.29/20.47  thf('39', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 20.29/20.47       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 20.29/20.47      inference('simplify', [status(thm)], ['38'])).
% 20.29/20.47  thf('40', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 20.29/20.47       ((v3_pre_topc @ sk_B @ sk_A))),
% 20.29/20.47      inference('split', [status(esa)], ['3'])).
% 20.29/20.47  thf('41', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf(dt_k2_tops_1, axiom,
% 20.29/20.47    (![A:$i,B:$i]:
% 20.29/20.47     ( ( ( l1_pre_topc @ A ) & 
% 20.29/20.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 20.29/20.47       ( m1_subset_1 @
% 20.29/20.47         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 20.29/20.47  thf('42', plain,
% 20.29/20.47      (![X67 : $i, X68 : $i]:
% 20.29/20.47         (~ (l1_pre_topc @ X67)
% 20.29/20.47          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 20.29/20.47          | (m1_subset_1 @ (k2_tops_1 @ X67 @ X68) @ 
% 20.29/20.47             (k1_zfmisc_1 @ (u1_struct_0 @ X67))))),
% 20.29/20.47      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 20.29/20.47  thf('43', plain,
% 20.29/20.47      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 20.29/20.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.29/20.47        | ~ (l1_pre_topc @ sk_A))),
% 20.29/20.47      inference('sup-', [status(thm)], ['41', '42'])).
% 20.29/20.47  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('45', plain,
% 20.29/20.47      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 20.29/20.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('demod', [status(thm)], ['43', '44'])).
% 20.29/20.47  thf('46', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf(dt_k4_subset_1, axiom,
% 20.29/20.47    (![A:$i,B:$i,C:$i]:
% 20.29/20.47     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 20.29/20.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 20.29/20.47       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 20.29/20.47  thf('47', plain,
% 20.29/20.47      (![X35 : $i, X36 : $i, X37 : $i]:
% 20.29/20.47         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 20.29/20.47          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 20.29/20.47          | (m1_subset_1 @ (k4_subset_1 @ X36 @ X35 @ X37) @ 
% 20.29/20.47             (k1_zfmisc_1 @ X36)))),
% 20.29/20.47      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 20.29/20.47  thf('48', plain,
% 20.29/20.47      (![X0 : $i]:
% 20.29/20.47         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 20.29/20.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.29/20.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 20.29/20.47      inference('sup-', [status(thm)], ['46', '47'])).
% 20.29/20.47  thf('49', plain,
% 20.29/20.47      ((m1_subset_1 @ 
% 20.29/20.47        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 20.29/20.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('sup-', [status(thm)], ['45', '48'])).
% 20.29/20.47  thf('50', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf(t65_tops_1, axiom,
% 20.29/20.47    (![A:$i]:
% 20.29/20.47     ( ( l1_pre_topc @ A ) =>
% 20.29/20.47       ( ![B:$i]:
% 20.29/20.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.29/20.47           ( ( k2_pre_topc @ A @ B ) =
% 20.29/20.47             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 20.29/20.47  thf('51', plain,
% 20.29/20.47      (![X78 : $i, X79 : $i]:
% 20.29/20.47         (~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (u1_struct_0 @ X79)))
% 20.29/20.47          | ((k2_pre_topc @ X79 @ X78)
% 20.29/20.47              = (k4_subset_1 @ (u1_struct_0 @ X79) @ X78 @ 
% 20.29/20.47                 (k2_tops_1 @ X79 @ X78)))
% 20.29/20.47          | ~ (l1_pre_topc @ X79))),
% 20.29/20.47      inference('cnf', [status(esa)], [t65_tops_1])).
% 20.29/20.47  thf('52', plain,
% 20.29/20.47      ((~ (l1_pre_topc @ sk_A)
% 20.29/20.47        | ((k2_pre_topc @ sk_A @ sk_B)
% 20.29/20.47            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 20.29/20.47               (k2_tops_1 @ sk_A @ sk_B))))),
% 20.29/20.47      inference('sup-', [status(thm)], ['50', '51'])).
% 20.29/20.47  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('54', plain,
% 20.29/20.47      (((k2_pre_topc @ sk_A @ sk_B)
% 20.29/20.47         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 20.29/20.47            (k2_tops_1 @ sk_A @ sk_B)))),
% 20.29/20.47      inference('demod', [status(thm)], ['52', '53'])).
% 20.29/20.47  thf('55', plain,
% 20.29/20.47      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 20.29/20.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('demod', [status(thm)], ['49', '54'])).
% 20.29/20.47  thf('56', plain,
% 20.29/20.47      (![X49 : $i, X50 : $i, X51 : $i]:
% 20.29/20.47         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 20.29/20.47          | ((k7_subset_1 @ X50 @ X49 @ X51) = (k4_xboole_0 @ X49 @ X51)))),
% 20.29/20.47      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 20.29/20.47  thf('57', plain,
% 20.29/20.47      (![X0 : $i]:
% 20.29/20.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 20.29/20.47           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 20.29/20.47      inference('sup-', [status(thm)], ['55', '56'])).
% 20.29/20.47  thf('58', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 20.29/20.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 20.29/20.47      inference('split', [status(esa)], ['3'])).
% 20.29/20.47  thf('59', plain,
% 20.29/20.47      ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 20.29/20.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 20.29/20.47      inference('sup+', [status(thm)], ['57', '58'])).
% 20.29/20.47  thf('60', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 20.29/20.47      inference('simplify', [status(thm)], ['12'])).
% 20.29/20.47  thf(t28_xboole_1, axiom,
% 20.29/20.47    (![A:$i,B:$i]:
% 20.29/20.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 20.29/20.47  thf('61', plain,
% 20.29/20.47      (![X18 : $i, X19 : $i]:
% 20.29/20.47         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 20.29/20.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 20.29/20.47  thf('62', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 20.29/20.47      inference('sup-', [status(thm)], ['60', '61'])).
% 20.29/20.47  thf(t52_xboole_1, axiom,
% 20.29/20.47    (![A:$i,B:$i,C:$i]:
% 20.29/20.47     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 20.29/20.47       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 20.29/20.47  thf('63', plain,
% 20.29/20.47      (![X28 : $i, X29 : $i, X30 : $i]:
% 20.29/20.47         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X30))
% 20.29/20.47           = (k2_xboole_0 @ (k4_xboole_0 @ X28 @ X29) @ 
% 20.29/20.47              (k3_xboole_0 @ X28 @ X30)))),
% 20.29/20.47      inference('cnf', [status(esa)], [t52_xboole_1])).
% 20.29/20.47  thf('64', plain,
% 20.29/20.47      (![X0 : $i, X1 : $i]:
% 20.29/20.47         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 20.29/20.47           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 20.29/20.47      inference('sup+', [status(thm)], ['62', '63'])).
% 20.29/20.47  thf(commutativity_k2_xboole_0, axiom,
% 20.29/20.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 20.29/20.47  thf('65', plain,
% 20.29/20.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.29/20.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 20.29/20.47  thf('66', plain,
% 20.29/20.47      (![X0 : $i, X1 : $i]:
% 20.29/20.47         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 20.29/20.47           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 20.29/20.47      inference('demod', [status(thm)], ['64', '65'])).
% 20.29/20.47  thf('67', plain,
% 20.29/20.47      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 20.29/20.47      inference('cnf', [status(esa)], [t36_xboole_1])).
% 20.29/20.47  thf(t12_xboole_1, axiom,
% 20.29/20.47    (![A:$i,B:$i]:
% 20.29/20.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 20.29/20.47  thf('68', plain,
% 20.29/20.47      (![X12 : $i, X13 : $i]:
% 20.29/20.47         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 20.29/20.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 20.29/20.47  thf('69', plain,
% 20.29/20.47      (![X0 : $i, X1 : $i]:
% 20.29/20.47         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 20.29/20.47      inference('sup-', [status(thm)], ['67', '68'])).
% 20.29/20.47  thf('70', plain,
% 20.29/20.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 20.29/20.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 20.29/20.47  thf('71', plain,
% 20.29/20.47      (![X0 : $i, X1 : $i]:
% 20.29/20.47         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 20.29/20.47      inference('demod', [status(thm)], ['69', '70'])).
% 20.29/20.47  thf('72', plain,
% 20.29/20.47      (![X0 : $i, X1 : $i]:
% 20.29/20.47         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 20.29/20.47      inference('demod', [status(thm)], ['66', '71'])).
% 20.29/20.47  thf('73', plain,
% 20.29/20.47      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 20.29/20.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 20.29/20.47      inference('sup+', [status(thm)], ['59', '72'])).
% 20.29/20.47  thf('74', plain,
% 20.29/20.47      (((k1_tops_1 @ sk_A @ sk_B)
% 20.29/20.47         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 20.29/20.47      inference('demod', [status(thm)], ['19', '22'])).
% 20.29/20.47  thf('75', plain,
% 20.29/20.47      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 20.29/20.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 20.29/20.47      inference('sup+', [status(thm)], ['73', '74'])).
% 20.29/20.47  thf('76', plain,
% 20.29/20.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf(fc9_tops_1, axiom,
% 20.29/20.47    (![A:$i,B:$i]:
% 20.29/20.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 20.29/20.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 20.29/20.47       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 20.29/20.47  thf('77', plain,
% 20.29/20.47      (![X69 : $i, X70 : $i]:
% 20.29/20.47         (~ (l1_pre_topc @ X69)
% 20.29/20.47          | ~ (v2_pre_topc @ X69)
% 20.29/20.47          | ~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 20.29/20.47          | (v3_pre_topc @ (k1_tops_1 @ X69 @ X70) @ X69))),
% 20.29/20.47      inference('cnf', [status(esa)], [fc9_tops_1])).
% 20.29/20.47  thf('78', plain,
% 20.29/20.47      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 20.29/20.47        | ~ (v2_pre_topc @ sk_A)
% 20.29/20.47        | ~ (l1_pre_topc @ sk_A))),
% 20.29/20.47      inference('sup-', [status(thm)], ['76', '77'])).
% 20.29/20.47  thf('79', plain, ((v2_pre_topc @ sk_A)),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 20.29/20.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.29/20.47  thf('81', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 20.29/20.47      inference('demod', [status(thm)], ['78', '79', '80'])).
% 20.29/20.47  thf('82', plain,
% 20.29/20.47      (((v3_pre_topc @ sk_B @ sk_A))
% 20.29/20.47         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 20.29/20.47      inference('sup+', [status(thm)], ['75', '81'])).
% 20.29/20.47  thf('83', plain,
% 20.29/20.47      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 20.29/20.47      inference('split', [status(esa)], ['0'])).
% 20.29/20.47  thf('84', plain,
% 20.29/20.47      (~
% 20.29/20.47       (((k2_tops_1 @ sk_A @ sk_B)
% 20.29/20.47          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 20.29/20.47             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 20.29/20.47       ((v3_pre_topc @ sk_B @ sk_A))),
% 20.29/20.47      inference('sup-', [status(thm)], ['82', '83'])).
% 20.29/20.47  thf('85', plain, ($false),
% 20.29/20.47      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '84'])).
% 20.29/20.47  
% 20.29/20.47  % SZS output end Refutation
% 20.29/20.47  
% 20.29/20.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
