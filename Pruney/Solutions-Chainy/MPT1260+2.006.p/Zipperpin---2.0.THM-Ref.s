%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.keHLJSXXby

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:22 EST 2020

% Result     : Theorem 37.65s
% Output     : Refutation 37.65s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 870 expanded)
%              Number of leaves         :   52 ( 304 expanded)
%              Depth                    :   20
%              Number of atoms          : 2008 (8341 expanded)
%              Number of equality atoms :  131 ( 598 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
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
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k4_xboole_0 @ X47 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k6_subset_1 @ X47 @ X49 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k2_tops_1 @ X63 @ X62 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X63 ) @ ( k2_pre_topc @ X63 @ X62 ) @ ( k1_tops_1 @ X63 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( l1_pre_topc @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X58 @ X59 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X32 @ X31 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ( ( k2_pre_topc @ X70 @ X69 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X70 ) @ X69 @ ( k2_tops_1 @ X70 @ X69 ) ) )
      | ~ ( l1_pre_topc @ X70 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k6_subset_1 @ X47 @ X49 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('65',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('68',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('71',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('73',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('74',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X53 @ X54 ) )
      = ( k3_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('75',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ ( k6_subset_1 @ X21 @ X22 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('77',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('78',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('79',plain,(
    ! [X14: $i] :
      ( ( k6_subset_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('81',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('82',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('83',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X53 @ X54 ) )
      = ( k3_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('84',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','85'])).

thf('87',plain,(
    ! [X14: $i] :
      ( ( k6_subset_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('90',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('93',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('95',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('99',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X55: $i,X57: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('103',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k4_subset_1 @ X43 @ X42 @ X44 )
        = ( k2_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['88','105'])).

thf('107',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('109',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('111',plain,(
    ! [X55: $i,X57: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('113',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k3_subset_1 @ X41 @ ( k3_subset_1 @ X41 @ X40 ) )
        = X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('116',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('117',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k6_subset_1 @ X45 @ X46 )
      = ( k4_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('118',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k6_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('121',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k6_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('123',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('124',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ ( k6_subset_1 @ X21 @ X22 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','119','122','125'])).

thf('127',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('128',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('131',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['109','130'])).

thf('132',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('133',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['62','133'])).

thf('135',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['114','119','122','125'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('138',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('139',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) )
      | ( ( k7_subset_1 @ X51 @ X52 @ X50 )
        = ( k9_subset_1 @ X51 @ X52 @ ( k3_subset_1 @ X51 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['137','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('145',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X47 @ X49 )
        = ( k6_subset_1 @ X47 @ X49 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ X2 )
      = ( k6_subset_1 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['143','146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['136','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('151',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('152',plain,(
    ! [X55: $i,X57: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X57 ) )
      | ~ ( r1_tarski @ X55 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('153',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('154',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k9_subset_1 @ X38 @ X37 @ X37 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['149','150','155'])).

thf('157',plain,
    ( ( k6_subset_1 @ sk_B_1 @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['135','156'])).

thf('158',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['134','157'])).

thf('159',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('160',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('162',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( l1_pre_topc @ X60 )
      | ~ ( v2_pre_topc @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X60 @ X61 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('163',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['160','166'])).

thf('168',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('169',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','169'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.18  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.keHLJSXXby
% 0.17/0.38  % Computer   : n024.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 11:34:36 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.22/0.39  % Python version: Python 3.6.8
% 0.22/0.39  % Running in FO mode
% 37.65/37.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 37.65/37.89  % Solved by: fo/fo7.sh
% 37.65/37.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 37.65/37.89  % done 43706 iterations in 37.381s
% 37.65/37.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 37.65/37.89  % SZS output start Refutation
% 37.65/37.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 37.65/37.89  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 37.65/37.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 37.65/37.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 37.65/37.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 37.65/37.89  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 37.65/37.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 37.65/37.89  thf(sk_A_type, type, sk_A: $i).
% 37.65/37.89  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 37.65/37.89  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 37.65/37.89  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 37.65/37.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 37.65/37.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 37.65/37.89  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 37.65/37.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 37.65/37.89  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 37.65/37.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 37.65/37.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 37.65/37.89  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 37.65/37.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 37.65/37.89  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 37.65/37.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 37.65/37.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 37.65/37.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 37.65/37.89  thf(t76_tops_1, conjecture,
% 37.65/37.89    (![A:$i]:
% 37.65/37.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 37.65/37.89       ( ![B:$i]:
% 37.65/37.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 37.65/37.89           ( ( v3_pre_topc @ B @ A ) <=>
% 37.65/37.89             ( ( k2_tops_1 @ A @ B ) =
% 37.65/37.89               ( k7_subset_1 @
% 37.65/37.89                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 37.65/37.89  thf(zf_stmt_0, negated_conjecture,
% 37.65/37.89    (~( ![A:$i]:
% 37.65/37.89        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 37.65/37.89          ( ![B:$i]:
% 37.65/37.89            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 37.65/37.89              ( ( v3_pre_topc @ B @ A ) <=>
% 37.65/37.89                ( ( k2_tops_1 @ A @ B ) =
% 37.65/37.89                  ( k7_subset_1 @
% 37.65/37.89                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 37.65/37.89    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 37.65/37.89  thf('0', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 37.65/37.89        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('1', plain,
% 37.65/37.89      (~
% 37.65/37.89       (((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 37.65/37.89       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 37.65/37.89      inference('split', [status(esa)], ['0'])).
% 37.65/37.89  thf('2', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('3', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 37.65/37.89        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('4', plain,
% 37.65/37.89      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 37.65/37.89      inference('split', [status(esa)], ['3'])).
% 37.65/37.89  thf('5', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(t56_tops_1, axiom,
% 37.65/37.89    (![A:$i]:
% 37.65/37.89     ( ( l1_pre_topc @ A ) =>
% 37.65/37.89       ( ![B:$i]:
% 37.65/37.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 37.65/37.89           ( ![C:$i]:
% 37.65/37.89             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 37.65/37.89               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 37.65/37.89                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 37.65/37.89  thf('6', plain,
% 37.65/37.89      (![X64 : $i, X65 : $i, X66 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 37.65/37.89          | ~ (v3_pre_topc @ X64 @ X65)
% 37.65/37.89          | ~ (r1_tarski @ X64 @ X66)
% 37.65/37.89          | (r1_tarski @ X64 @ (k1_tops_1 @ X65 @ X66))
% 37.65/37.89          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 37.65/37.89          | ~ (l1_pre_topc @ X65))),
% 37.65/37.89      inference('cnf', [status(esa)], [t56_tops_1])).
% 37.65/37.89  thf('7', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         (~ (l1_pre_topc @ sk_A)
% 37.65/37.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 37.65/37.89          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 37.65/37.89          | ~ (r1_tarski @ sk_B_1 @ X0)
% 37.65/37.89          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 37.65/37.89      inference('sup-', [status(thm)], ['5', '6'])).
% 37.65/37.89  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('9', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 37.65/37.89          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 37.65/37.89          | ~ (r1_tarski @ sk_B_1 @ X0)
% 37.65/37.89          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 37.65/37.89      inference('demod', [status(thm)], ['7', '8'])).
% 37.65/37.89  thf('10', plain,
% 37.65/37.89      ((![X0 : $i]:
% 37.65/37.89          (~ (r1_tarski @ sk_B_1 @ X0)
% 37.65/37.89           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 37.65/37.89           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 37.65/37.89         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['4', '9'])).
% 37.65/37.89  thf('11', plain,
% 37.65/37.89      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 37.65/37.89         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 37.65/37.89         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['2', '10'])).
% 37.65/37.89  thf(d10_xboole_0, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 37.65/37.89  thf('12', plain,
% 37.65/37.89      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 37.65/37.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 37.65/37.89  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 37.65/37.89      inference('simplify', [status(thm)], ['12'])).
% 37.65/37.89  thf('14', plain,
% 37.65/37.89      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 37.65/37.89         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 37.65/37.89      inference('demod', [status(thm)], ['11', '13'])).
% 37.65/37.89  thf('15', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(t74_tops_1, axiom,
% 37.65/37.89    (![A:$i]:
% 37.65/37.89     ( ( l1_pre_topc @ A ) =>
% 37.65/37.89       ( ![B:$i]:
% 37.65/37.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 37.65/37.89           ( ( k1_tops_1 @ A @ B ) =
% 37.65/37.89             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 37.65/37.89  thf('16', plain,
% 37.65/37.89      (![X71 : $i, X72 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 37.65/37.89          | ((k1_tops_1 @ X72 @ X71)
% 37.65/37.89              = (k7_subset_1 @ (u1_struct_0 @ X72) @ X71 @ 
% 37.65/37.89                 (k2_tops_1 @ X72 @ X71)))
% 37.65/37.89          | ~ (l1_pre_topc @ X72))),
% 37.65/37.89      inference('cnf', [status(esa)], [t74_tops_1])).
% 37.65/37.89  thf('17', plain,
% 37.65/37.89      ((~ (l1_pre_topc @ sk_A)
% 37.65/37.89        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 37.65/37.89               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 37.65/37.89      inference('sup-', [status(thm)], ['15', '16'])).
% 37.65/37.89  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('19', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(redefinition_k7_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i,C:$i]:
% 37.65/37.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 37.65/37.89       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 37.65/37.89  thf('20', plain,
% 37.65/37.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 37.65/37.89          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k4_xboole_0 @ X47 @ X49)))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 37.65/37.89  thf(redefinition_k6_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 37.65/37.89  thf('21', plain,
% 37.65/37.89      (![X45 : $i, X46 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 37.65/37.89  thf('22', plain,
% 37.65/37.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 37.65/37.89          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k6_subset_1 @ X47 @ X49)))),
% 37.65/37.89      inference('demod', [status(thm)], ['20', '21'])).
% 37.65/37.89  thf('23', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 37.65/37.89           = (k6_subset_1 @ sk_B_1 @ X0))),
% 37.65/37.89      inference('sup-', [status(thm)], ['19', '22'])).
% 37.65/37.89  thf('24', plain,
% 37.65/37.89      (((k1_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['17', '18', '23'])).
% 37.65/37.89  thf(dt_k6_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 37.65/37.89  thf('25', plain,
% 37.65/37.89      (![X34 : $i, X35 : $i]:
% 37.65/37.89         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 37.65/37.89      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 37.65/37.89  thf(t3_subset, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 37.65/37.89  thf('26', plain,
% 37.65/37.89      (![X55 : $i, X56 : $i]:
% 37.65/37.89         ((r1_tarski @ X55 @ X56) | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56)))),
% 37.65/37.89      inference('cnf', [status(esa)], [t3_subset])).
% 37.65/37.89  thf('27', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 37.65/37.89      inference('sup-', [status(thm)], ['25', '26'])).
% 37.65/37.89  thf('28', plain,
% 37.65/37.89      (![X2 : $i, X4 : $i]:
% 37.65/37.89         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 37.65/37.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 37.65/37.89  thf('29', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 37.65/37.89          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['27', '28'])).
% 37.65/37.89  thf('30', plain,
% 37.65/37.89      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 37.65/37.89        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 37.65/37.89      inference('sup-', [status(thm)], ['24', '29'])).
% 37.65/37.89  thf('31', plain,
% 37.65/37.89      (((k1_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['17', '18', '23'])).
% 37.65/37.89  thf('32', plain,
% 37.65/37.89      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 37.65/37.89        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['30', '31'])).
% 37.65/37.89  thf('33', plain,
% 37.65/37.89      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 37.65/37.89         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['14', '32'])).
% 37.65/37.89  thf('34', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(l78_tops_1, axiom,
% 37.65/37.89    (![A:$i]:
% 37.65/37.89     ( ( l1_pre_topc @ A ) =>
% 37.65/37.89       ( ![B:$i]:
% 37.65/37.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 37.65/37.89           ( ( k2_tops_1 @ A @ B ) =
% 37.65/37.89             ( k7_subset_1 @
% 37.65/37.89               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 37.65/37.89               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 37.65/37.89  thf('35', plain,
% 37.65/37.89      (![X62 : $i, X63 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 37.65/37.89          | ((k2_tops_1 @ X63 @ X62)
% 37.65/37.89              = (k7_subset_1 @ (u1_struct_0 @ X63) @ 
% 37.65/37.89                 (k2_pre_topc @ X63 @ X62) @ (k1_tops_1 @ X63 @ X62)))
% 37.65/37.89          | ~ (l1_pre_topc @ X63))),
% 37.65/37.89      inference('cnf', [status(esa)], [l78_tops_1])).
% 37.65/37.89  thf('36', plain,
% 37.65/37.89      ((~ (l1_pre_topc @ sk_A)
% 37.65/37.89        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 37.65/37.89      inference('sup-', [status(thm)], ['34', '35'])).
% 37.65/37.89  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('38', plain,
% 37.65/37.89      (((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['36', '37'])).
% 37.65/37.89  thf('39', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 37.65/37.89         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 37.65/37.89      inference('sup+', [status(thm)], ['33', '38'])).
% 37.65/37.89  thf('40', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 37.65/37.89         <= (~
% 37.65/37.89             (((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 37.65/37.89      inference('split', [status(esa)], ['0'])).
% 37.65/37.89  thf('41', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 37.65/37.89         <= (~
% 37.65/37.89             (((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 37.65/37.89             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['39', '40'])).
% 37.65/37.89  thf('42', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 37.65/37.89       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 37.65/37.89      inference('simplify', [status(thm)], ['41'])).
% 37.65/37.89  thf('43', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 37.65/37.89       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 37.65/37.89      inference('split', [status(esa)], ['3'])).
% 37.65/37.89  thf('44', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(dt_k2_tops_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( ( l1_pre_topc @ A ) & 
% 37.65/37.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 37.65/37.89       ( m1_subset_1 @
% 37.65/37.89         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 37.65/37.89  thf('45', plain,
% 37.65/37.89      (![X58 : $i, X59 : $i]:
% 37.65/37.89         (~ (l1_pre_topc @ X58)
% 37.65/37.89          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 37.65/37.89          | (m1_subset_1 @ (k2_tops_1 @ X58 @ X59) @ 
% 37.65/37.89             (k1_zfmisc_1 @ (u1_struct_0 @ X58))))),
% 37.65/37.89      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 37.65/37.89  thf('46', plain,
% 37.65/37.89      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 37.65/37.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 37.65/37.89        | ~ (l1_pre_topc @ sk_A))),
% 37.65/37.89      inference('sup-', [status(thm)], ['44', '45'])).
% 37.65/37.89  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('48', plain,
% 37.65/37.89      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 37.65/37.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('demod', [status(thm)], ['46', '47'])).
% 37.65/37.89  thf('49', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(dt_k4_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i,C:$i]:
% 37.65/37.89     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 37.65/37.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 37.65/37.89       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 37.65/37.89  thf('50', plain,
% 37.65/37.89      (![X31 : $i, X32 : $i, X33 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 37.65/37.89          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 37.65/37.89          | (m1_subset_1 @ (k4_subset_1 @ X32 @ X31 @ X33) @ 
% 37.65/37.89             (k1_zfmisc_1 @ X32)))),
% 37.65/37.89      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 37.65/37.89  thf('51', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 37.65/37.89           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 37.65/37.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 37.65/37.89      inference('sup-', [status(thm)], ['49', '50'])).
% 37.65/37.89  thf('52', plain,
% 37.65/37.89      ((m1_subset_1 @ 
% 37.65/37.89        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 37.65/37.89         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 37.65/37.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['48', '51'])).
% 37.65/37.89  thf('53', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(t65_tops_1, axiom,
% 37.65/37.89    (![A:$i]:
% 37.65/37.89     ( ( l1_pre_topc @ A ) =>
% 37.65/37.89       ( ![B:$i]:
% 37.65/37.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 37.65/37.89           ( ( k2_pre_topc @ A @ B ) =
% 37.65/37.89             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 37.65/37.89  thf('54', plain,
% 37.65/37.89      (![X69 : $i, X70 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 37.65/37.89          | ((k2_pre_topc @ X70 @ X69)
% 37.65/37.89              = (k4_subset_1 @ (u1_struct_0 @ X70) @ X69 @ 
% 37.65/37.89                 (k2_tops_1 @ X70 @ X69)))
% 37.65/37.89          | ~ (l1_pre_topc @ X70))),
% 37.65/37.89      inference('cnf', [status(esa)], [t65_tops_1])).
% 37.65/37.89  thf('55', plain,
% 37.65/37.89      ((~ (l1_pre_topc @ sk_A)
% 37.65/37.89        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 37.65/37.89            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 37.65/37.89               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 37.65/37.89      inference('sup-', [status(thm)], ['53', '54'])).
% 37.65/37.89  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('57', plain,
% 37.65/37.89      (((k2_pre_topc @ sk_A @ sk_B_1)
% 37.65/37.89         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 37.65/37.89            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['55', '56'])).
% 37.65/37.89  thf('58', plain,
% 37.65/37.89      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 37.65/37.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('demod', [status(thm)], ['52', '57'])).
% 37.65/37.89  thf('59', plain,
% 37.65/37.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 37.65/37.89          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k6_subset_1 @ X47 @ X49)))),
% 37.65/37.89      inference('demod', [status(thm)], ['20', '21'])).
% 37.65/37.89  thf('60', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 37.65/37.89           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 37.65/37.89      inference('sup-', [status(thm)], ['58', '59'])).
% 37.65/37.89  thf('61', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 37.65/37.89         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 37.65/37.89      inference('split', [status(esa)], ['3'])).
% 37.65/37.89  thf('62', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 37.65/37.89         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 37.65/37.89      inference('sup+', [status(thm)], ['60', '61'])).
% 37.65/37.89  thf(t7_xboole_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 37.65/37.89  thf('63', plain,
% 37.65/37.89      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 37.65/37.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 37.65/37.89  thf(t43_xboole_1, axiom,
% 37.65/37.89    (![A:$i,B:$i,C:$i]:
% 37.65/37.89     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 37.65/37.89       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 37.65/37.89  thf('64', plain,
% 37.65/37.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 37.65/37.89         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 37.65/37.89          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 37.65/37.89      inference('cnf', [status(esa)], [t43_xboole_1])).
% 37.65/37.89  thf('65', plain,
% 37.65/37.89      (![X45 : $i, X46 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 37.65/37.89  thf('66', plain,
% 37.65/37.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 37.65/37.89         ((r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18)
% 37.65/37.89          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 37.65/37.89      inference('demod', [status(thm)], ['64', '65'])).
% 37.65/37.89  thf('67', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 37.65/37.89      inference('sup-', [status(thm)], ['63', '66'])).
% 37.65/37.89  thf(t3_xboole_1, axiom,
% 37.65/37.89    (![A:$i]:
% 37.65/37.89     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 37.65/37.89  thf('68', plain,
% 37.65/37.89      (![X15 : $i]:
% 37.65/37.89         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 37.65/37.89      inference('cnf', [status(esa)], [t3_xboole_1])).
% 37.65/37.89  thf('69', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 37.65/37.89      inference('sup-', [status(thm)], ['67', '68'])).
% 37.65/37.89  thf('70', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 37.65/37.89      inference('sup-', [status(thm)], ['67', '68'])).
% 37.65/37.89  thf(t48_xboole_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 37.65/37.89  thf('71', plain,
% 37.65/37.89      (![X21 : $i, X22 : $i]:
% 37.65/37.89         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 37.65/37.89           = (k3_xboole_0 @ X21 @ X22))),
% 37.65/37.89      inference('cnf', [status(esa)], [t48_xboole_1])).
% 37.65/37.89  thf('72', plain,
% 37.65/37.89      (![X45 : $i, X46 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 37.65/37.89  thf('73', plain,
% 37.65/37.89      (![X45 : $i, X46 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 37.65/37.89  thf(t12_setfam_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 37.65/37.89  thf('74', plain,
% 37.65/37.89      (![X53 : $i, X54 : $i]:
% 37.65/37.89         ((k1_setfam_1 @ (k2_tarski @ X53 @ X54)) = (k3_xboole_0 @ X53 @ X54))),
% 37.65/37.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 37.65/37.89  thf('75', plain,
% 37.65/37.89      (![X21 : $i, X22 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X21 @ (k6_subset_1 @ X21 @ X22))
% 37.65/37.89           = (k1_setfam_1 @ (k2_tarski @ X21 @ X22)))),
% 37.65/37.89      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 37.65/37.89  thf('76', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X0 @ k1_xboole_0)
% 37.65/37.89           = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 37.65/37.89      inference('sup+', [status(thm)], ['70', '75'])).
% 37.65/37.89  thf(t3_boole, axiom,
% 37.65/37.89    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 37.65/37.89  thf('77', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 37.65/37.89      inference('cnf', [status(esa)], [t3_boole])).
% 37.65/37.89  thf('78', plain,
% 37.65/37.89      (![X45 : $i, X46 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 37.65/37.89  thf('79', plain, (![X14 : $i]: ((k6_subset_1 @ X14 @ k1_xboole_0) = (X14))),
% 37.65/37.89      inference('demod', [status(thm)], ['77', '78'])).
% 37.65/37.89  thf('80', plain,
% 37.65/37.89      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 37.65/37.89      inference('demod', [status(thm)], ['76', '79'])).
% 37.65/37.89  thf(t100_xboole_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 37.65/37.89  thf('81', plain,
% 37.65/37.89      (![X5 : $i, X6 : $i]:
% 37.65/37.89         ((k4_xboole_0 @ X5 @ X6)
% 37.65/37.89           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 37.65/37.89      inference('cnf', [status(esa)], [t100_xboole_1])).
% 37.65/37.89  thf('82', plain,
% 37.65/37.89      (![X45 : $i, X46 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 37.65/37.89  thf('83', plain,
% 37.65/37.89      (![X53 : $i, X54 : $i]:
% 37.65/37.89         ((k1_setfam_1 @ (k2_tarski @ X53 @ X54)) = (k3_xboole_0 @ X53 @ X54))),
% 37.65/37.89      inference('cnf', [status(esa)], [t12_setfam_1])).
% 37.65/37.89  thf('84', plain,
% 37.65/37.89      (![X5 : $i, X6 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X5 @ X6)
% 37.65/37.89           = (k5_xboole_0 @ X5 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 37.65/37.89      inference('demod', [status(thm)], ['81', '82', '83'])).
% 37.65/37.89  thf('85', plain,
% 37.65/37.89      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 37.65/37.89      inference('sup+', [status(thm)], ['80', '84'])).
% 37.65/37.89  thf('86', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 37.65/37.89      inference('demod', [status(thm)], ['69', '85'])).
% 37.65/37.89  thf('87', plain, (![X14 : $i]: ((k6_subset_1 @ X14 @ k1_xboole_0) = (X14))),
% 37.65/37.89      inference('demod', [status(thm)], ['77', '78'])).
% 37.65/37.89  thf('88', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 37.65/37.89      inference('sup+', [status(thm)], ['86', '87'])).
% 37.65/37.89  thf(commutativity_k2_xboole_0, axiom,
% 37.65/37.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 37.65/37.89  thf('89', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 37.65/37.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 37.65/37.89  thf('90', plain,
% 37.65/37.89      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 37.65/37.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 37.65/37.89  thf('91', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 37.65/37.89      inference('sup+', [status(thm)], ['89', '90'])).
% 37.65/37.89  thf('92', plain,
% 37.65/37.89      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 37.65/37.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('demod', [status(thm)], ['46', '47'])).
% 37.65/37.89  thf('93', plain,
% 37.65/37.89      (![X55 : $i, X56 : $i]:
% 37.65/37.89         ((r1_tarski @ X55 @ X56) | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56)))),
% 37.65/37.89      inference('cnf', [status(esa)], [t3_subset])).
% 37.65/37.89  thf('94', plain,
% 37.65/37.89      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 37.65/37.89      inference('sup-', [status(thm)], ['92', '93'])).
% 37.65/37.89  thf(t1_xboole_1, axiom,
% 37.65/37.89    (![A:$i,B:$i,C:$i]:
% 37.65/37.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 37.65/37.89       ( r1_tarski @ A @ C ) ))).
% 37.65/37.89  thf('95', plain,
% 37.65/37.89      (![X9 : $i, X10 : $i, X11 : $i]:
% 37.65/37.89         (~ (r1_tarski @ X9 @ X10)
% 37.65/37.89          | ~ (r1_tarski @ X10 @ X11)
% 37.65/37.89          | (r1_tarski @ X9 @ X11))),
% 37.65/37.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 37.65/37.89  thf('96', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ X0)
% 37.65/37.89          | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 37.65/37.89      inference('sup-', [status(thm)], ['94', '95'])).
% 37.65/37.89  thf('97', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 37.65/37.89          (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['91', '96'])).
% 37.65/37.89  thf('98', plain,
% 37.65/37.89      (![X16 : $i, X17 : $i, X18 : $i]:
% 37.65/37.89         ((r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18)
% 37.65/37.89          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 37.65/37.89      inference('demod', [status(thm)], ['64', '65'])).
% 37.65/37.89  thf('99', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         (r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ X0) @ 
% 37.65/37.89          (u1_struct_0 @ sk_A))),
% 37.65/37.89      inference('sup-', [status(thm)], ['97', '98'])).
% 37.65/37.89  thf('100', plain,
% 37.65/37.89      (![X55 : $i, X57 : $i]:
% 37.65/37.89         ((m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X57)) | ~ (r1_tarski @ X55 @ X57))),
% 37.65/37.89      inference('cnf', [status(esa)], [t3_subset])).
% 37.65/37.89  thf('101', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         (m1_subset_1 @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ X0) @ 
% 37.65/37.89          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['99', '100'])).
% 37.65/37.89  thf('102', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(redefinition_k4_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i,C:$i]:
% 37.65/37.89     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 37.65/37.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 37.65/37.89       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 37.65/37.89  thf('103', plain,
% 37.65/37.89      (![X42 : $i, X43 : $i, X44 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 37.65/37.89          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43))
% 37.65/37.89          | ((k4_subset_1 @ X43 @ X42 @ X44) = (k2_xboole_0 @ X42 @ X44)))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 37.65/37.89  thf('104', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 37.65/37.89            = (k2_xboole_0 @ sk_B_1 @ X0))
% 37.65/37.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 37.65/37.89      inference('sup-', [status(thm)], ['102', '103'])).
% 37.65/37.89  thf('105', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 37.65/37.89           (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ X0))
% 37.65/37.89           = (k2_xboole_0 @ sk_B_1 @ 
% 37.65/37.89              (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ X0)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['101', '104'])).
% 37.65/37.89  thf('106', plain,
% 37.65/37.89      (![X0 : $i]:
% 37.65/37.89         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 37.65/37.89           (k2_tops_1 @ sk_A @ sk_B_1))
% 37.65/37.89           = (k2_xboole_0 @ sk_B_1 @ 
% 37.65/37.89              (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 37.65/37.89               (k5_xboole_0 @ X0 @ X0))))),
% 37.65/37.89      inference('sup+', [status(thm)], ['88', '105'])).
% 37.65/37.89  thf('107', plain,
% 37.65/37.89      (((k2_pre_topc @ sk_A @ sk_B_1)
% 37.65/37.89         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 37.65/37.89            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['55', '56'])).
% 37.65/37.89  thf('108', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 37.65/37.89      inference('sup+', [status(thm)], ['86', '87'])).
% 37.65/37.89  thf('109', plain,
% 37.65/37.89      (((k2_pre_topc @ sk_A @ sk_B_1)
% 37.65/37.89         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['106', '107', '108'])).
% 37.65/37.89  thf('110', plain,
% 37.65/37.89      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 37.65/37.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 37.65/37.89  thf('111', plain,
% 37.65/37.89      (![X55 : $i, X57 : $i]:
% 37.65/37.89         ((m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X57)) | ~ (r1_tarski @ X55 @ X57))),
% 37.65/37.89      inference('cnf', [status(esa)], [t3_subset])).
% 37.65/37.89  thf('112', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['110', '111'])).
% 37.65/37.89  thf(involutiveness_k3_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 37.65/37.89       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 37.65/37.89  thf('113', plain,
% 37.65/37.89      (![X40 : $i, X41 : $i]:
% 37.65/37.89         (((k3_subset_1 @ X41 @ (k3_subset_1 @ X41 @ X40)) = (X40))
% 37.65/37.89          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 37.65/37.89      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 37.65/37.89  thf('114', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 37.65/37.89           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 37.65/37.89      inference('sup-', [status(thm)], ['112', '113'])).
% 37.65/37.89  thf('115', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['110', '111'])).
% 37.65/37.89  thf(d5_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 37.65/37.89       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 37.65/37.89  thf('116', plain,
% 37.65/37.89      (![X27 : $i, X28 : $i]:
% 37.65/37.89         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 37.65/37.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 37.65/37.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 37.65/37.89  thf('117', plain,
% 37.65/37.89      (![X45 : $i, X46 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X45 @ X46) = (k4_xboole_0 @ X45 @ X46))),
% 37.65/37.89      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 37.65/37.89  thf('118', plain,
% 37.65/37.89      (![X27 : $i, X28 : $i]:
% 37.65/37.89         (((k3_subset_1 @ X27 @ X28) = (k6_subset_1 @ X27 @ X28))
% 37.65/37.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 37.65/37.89      inference('demod', [status(thm)], ['116', '117'])).
% 37.65/37.89  thf('119', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 37.65/37.89           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 37.65/37.89      inference('sup-', [status(thm)], ['115', '118'])).
% 37.65/37.89  thf('120', plain,
% 37.65/37.89      (![X34 : $i, X35 : $i]:
% 37.65/37.89         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 37.65/37.89      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 37.65/37.89  thf('121', plain,
% 37.65/37.89      (![X27 : $i, X28 : $i]:
% 37.65/37.89         (((k3_subset_1 @ X27 @ X28) = (k6_subset_1 @ X27 @ X28))
% 37.65/37.89          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 37.65/37.89      inference('demod', [status(thm)], ['116', '117'])).
% 37.65/37.89  thf('122', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 37.65/37.89           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['120', '121'])).
% 37.65/37.89  thf(commutativity_k2_tarski, axiom,
% 37.65/37.89    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 37.65/37.89  thf('123', plain,
% 37.65/37.89      (![X25 : $i, X26 : $i]:
% 37.65/37.89         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 37.65/37.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 37.65/37.89  thf('124', plain,
% 37.65/37.89      (![X21 : $i, X22 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X21 @ (k6_subset_1 @ X21 @ X22))
% 37.65/37.89           = (k1_setfam_1 @ (k2_tarski @ X21 @ X22)))),
% 37.65/37.89      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 37.65/37.89  thf('125', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 37.65/37.89           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 37.65/37.89      inference('sup+', [status(thm)], ['123', '124'])).
% 37.65/37.89  thf('126', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (X1))),
% 37.65/37.89      inference('demod', [status(thm)], ['114', '119', '122', '125'])).
% 37.65/37.89  thf('127', plain,
% 37.65/37.89      (![X25 : $i, X26 : $i]:
% 37.65/37.89         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 37.65/37.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 37.65/37.89  thf('128', plain,
% 37.65/37.89      (![X5 : $i, X6 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X5 @ X6)
% 37.65/37.89           = (k5_xboole_0 @ X5 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 37.65/37.89      inference('demod', [status(thm)], ['81', '82', '83'])).
% 37.65/37.89  thf('129', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X0 @ X1)
% 37.65/37.89           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 37.65/37.89      inference('sup+', [status(thm)], ['127', '128'])).
% 37.65/37.89  thf('130', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 37.65/37.89           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 37.65/37.89      inference('sup+', [status(thm)], ['126', '129'])).
% 37.65/37.89  thf('131', plain,
% 37.65/37.89      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 37.65/37.89         = (k5_xboole_0 @ 
% 37.65/37.89            (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ sk_B_1))),
% 37.65/37.89      inference('sup+', [status(thm)], ['109', '130'])).
% 37.65/37.89  thf('132', plain,
% 37.65/37.89      (((k2_pre_topc @ sk_A @ sk_B_1)
% 37.65/37.89         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['106', '107', '108'])).
% 37.65/37.89  thf('133', plain,
% 37.65/37.89      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 37.65/37.89         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 37.65/37.89      inference('demod', [status(thm)], ['131', '132'])).
% 37.65/37.89  thf('134', plain,
% 37.65/37.89      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 37.65/37.89         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 37.65/37.89      inference('sup+', [status(thm)], ['62', '133'])).
% 37.65/37.89  thf('135', plain,
% 37.65/37.89      (((k2_pre_topc @ sk_A @ sk_B_1)
% 37.65/37.89         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['106', '107', '108'])).
% 37.65/37.89  thf('136', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (X1))),
% 37.65/37.89      inference('demod', [status(thm)], ['114', '119', '122', '125'])).
% 37.65/37.89  thf('137', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['110', '111'])).
% 37.65/37.89  thf('138', plain,
% 37.65/37.89      (![X34 : $i, X35 : $i]:
% 37.65/37.89         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 37.65/37.89      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 37.65/37.89  thf(t32_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 37.65/37.89       ( ![C:$i]:
% 37.65/37.89         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 37.65/37.89           ( ( k7_subset_1 @ A @ B @ C ) =
% 37.65/37.89             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 37.65/37.89  thf('139', plain,
% 37.65/37.89      (![X50 : $i, X51 : $i, X52 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51))
% 37.65/37.89          | ((k7_subset_1 @ X51 @ X52 @ X50)
% 37.65/37.89              = (k9_subset_1 @ X51 @ X52 @ (k3_subset_1 @ X51 @ X50)))
% 37.65/37.89          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X51)))),
% 37.65/37.89      inference('cnf', [status(esa)], [t32_subset_1])).
% 37.65/37.89  thf('140', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 37.65/37.89          | ((k7_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 37.65/37.89              = (k9_subset_1 @ X0 @ X2 @ 
% 37.65/37.89                 (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))))),
% 37.65/37.89      inference('sup-', [status(thm)], ['138', '139'])).
% 37.65/37.89  thf('141', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 37.65/37.89           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['120', '121'])).
% 37.65/37.89  thf('142', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 37.65/37.89          | ((k7_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 37.65/37.89              = (k9_subset_1 @ X0 @ X2 @ 
% 37.65/37.89                 (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))))),
% 37.65/37.89      inference('demod', [status(thm)], ['140', '141'])).
% 37.65/37.89  thf('143', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.65/37.89         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ 
% 37.65/37.89           (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 37.65/37.89           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ 
% 37.65/37.89              (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 37.65/37.89               (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 37.65/37.89      inference('sup-', [status(thm)], ['137', '142'])).
% 37.65/37.89  thf('144', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 37.65/37.89      inference('sup-', [status(thm)], ['110', '111'])).
% 37.65/37.89  thf('145', plain,
% 37.65/37.89      (![X47 : $i, X48 : $i, X49 : $i]:
% 37.65/37.89         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 37.65/37.89          | ((k7_subset_1 @ X48 @ X47 @ X49) = (k6_subset_1 @ X47 @ X49)))),
% 37.65/37.89      inference('demod', [status(thm)], ['20', '21'])).
% 37.65/37.89  thf('146', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.65/37.89         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ X2)
% 37.65/37.89           = (k6_subset_1 @ X1 @ X2))),
% 37.65/37.89      inference('sup-', [status(thm)], ['144', '145'])).
% 37.65/37.89  thf('147', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 37.65/37.89           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 37.65/37.89      inference('sup+', [status(thm)], ['123', '124'])).
% 37.65/37.89  thf('148', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X1 @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 37.65/37.89           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ 
% 37.65/37.89              (k1_setfam_1 @ (k2_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 37.65/37.89      inference('demod', [status(thm)], ['143', '146', '147'])).
% 37.65/37.89  thf('149', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X0 @ (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 37.65/37.89           = (k9_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0 @ X0))),
% 37.65/37.89      inference('sup+', [status(thm)], ['136', '148'])).
% 37.65/37.89  thf('150', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 37.65/37.89           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 37.65/37.89      inference('sup+', [status(thm)], ['126', '129'])).
% 37.65/37.89  thf('151', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 37.65/37.89      inference('simplify', [status(thm)], ['12'])).
% 37.65/37.89  thf('152', plain,
% 37.65/37.89      (![X55 : $i, X57 : $i]:
% 37.65/37.89         ((m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X57)) | ~ (r1_tarski @ X55 @ X57))),
% 37.65/37.89      inference('cnf', [status(esa)], [t3_subset])).
% 37.65/37.89  thf('153', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 37.65/37.89      inference('sup-', [status(thm)], ['151', '152'])).
% 37.65/37.89  thf(idempotence_k9_subset_1, axiom,
% 37.65/37.89    (![A:$i,B:$i,C:$i]:
% 37.65/37.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 37.65/37.89       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 37.65/37.89  thf('154', plain,
% 37.65/37.89      (![X37 : $i, X38 : $i, X39 : $i]:
% 37.65/37.89         (((k9_subset_1 @ X38 @ X37 @ X37) = (X37))
% 37.65/37.89          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 37.65/37.89      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 37.65/37.89  thf('155', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 37.65/37.89      inference('sup-', [status(thm)], ['153', '154'])).
% 37.65/37.89  thf('156', plain,
% 37.65/37.89      (![X0 : $i, X1 : $i]:
% 37.65/37.89         ((k6_subset_1 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 37.65/37.89           = (X0))),
% 37.65/37.89      inference('demod', [status(thm)], ['149', '150', '155'])).
% 37.65/37.89  thf('157', plain,
% 37.65/37.89      (((k6_subset_1 @ sk_B_1 @ 
% 37.65/37.89         (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 37.65/37.89      inference('sup+', [status(thm)], ['135', '156'])).
% 37.65/37.89  thf('158', plain,
% 37.65/37.89      ((((k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 37.65/37.89         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 37.65/37.89      inference('sup+', [status(thm)], ['134', '157'])).
% 37.65/37.89  thf('159', plain,
% 37.65/37.89      (((k1_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 37.65/37.89      inference('demod', [status(thm)], ['17', '18', '23'])).
% 37.65/37.89  thf('160', plain,
% 37.65/37.89      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 37.65/37.89         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 37.65/37.89      inference('sup+', [status(thm)], ['158', '159'])).
% 37.65/37.89  thf('161', plain,
% 37.65/37.89      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf(fc9_tops_1, axiom,
% 37.65/37.89    (![A:$i,B:$i]:
% 37.65/37.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 37.65/37.89         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 37.65/37.89       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 37.65/37.89  thf('162', plain,
% 37.65/37.89      (![X60 : $i, X61 : $i]:
% 37.65/37.89         (~ (l1_pre_topc @ X60)
% 37.65/37.89          | ~ (v2_pre_topc @ X60)
% 37.65/37.89          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 37.65/37.89          | (v3_pre_topc @ (k1_tops_1 @ X60 @ X61) @ X60))),
% 37.65/37.89      inference('cnf', [status(esa)], [fc9_tops_1])).
% 37.65/37.89  thf('163', plain,
% 37.65/37.89      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 37.65/37.89        | ~ (v2_pre_topc @ sk_A)
% 37.65/37.89        | ~ (l1_pre_topc @ sk_A))),
% 37.65/37.89      inference('sup-', [status(thm)], ['161', '162'])).
% 37.65/37.89  thf('164', plain, ((v2_pre_topc @ sk_A)),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 37.65/37.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.65/37.89  thf('166', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 37.65/37.89      inference('demod', [status(thm)], ['163', '164', '165'])).
% 37.65/37.89  thf('167', plain,
% 37.65/37.89      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 37.65/37.89         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 37.65/37.89      inference('sup+', [status(thm)], ['160', '166'])).
% 37.65/37.89  thf('168', plain,
% 37.65/37.89      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 37.65/37.89      inference('split', [status(esa)], ['0'])).
% 37.65/37.89  thf('169', plain,
% 37.65/37.89      (~
% 37.65/37.89       (((k2_tops_1 @ sk_A @ sk_B_1)
% 37.65/37.89          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 37.65/37.89             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 37.65/37.89       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 37.65/37.89      inference('sup-', [status(thm)], ['167', '168'])).
% 37.65/37.89  thf('170', plain, ($false),
% 37.65/37.89      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '169'])).
% 37.65/37.89  
% 37.65/37.89  % SZS output end Refutation
% 37.65/37.89  
% 37.65/37.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
