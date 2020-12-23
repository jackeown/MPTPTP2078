%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.se1CCBLcPt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:33 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 261 expanded)
%              Number of leaves         :   41 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          : 1327 (3115 expanded)
%              Number of equality atoms :   84 ( 187 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v3_pre_topc @ X43 @ X44 )
      | ~ ( r1_tarski @ X43 @ X45 )
      | ( r1_tarski @ X43 @ ( k1_tops_1 @ X44 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
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
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k1_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k4_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k6_subset_1 @ X29 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( ( k2_tops_1 @ X42 @ X41 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_pre_topc @ X42 @ X41 ) @ ( k1_tops_1 @ X42 @ X41 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X23 @ X22 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k2_pre_topc @ X47 @ X46 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X47 ) @ X46 @ ( k2_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k7_subset_1 @ X30 @ X29 @ X31 )
        = ( k6_subset_1 @ X29 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('63',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('64',plain,(
    ! [X19: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('66',plain,(
    ! [X19: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('67',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['71'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k6_subset_1 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['62','80'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('84',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k6_subset_1 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X19: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('88',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k6_subset_1 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('91',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['85','92'])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('97',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X39 @ X40 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('98',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','101'])).

thf('103',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.se1CCBLcPt
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.08  % Solved by: fo/fo7.sh
% 0.89/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.08  % done 1069 iterations in 0.621s
% 0.89/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.08  % SZS output start Refutation
% 0.89/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.08  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.89/1.08  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.89/1.08  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.89/1.08  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.89/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.89/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.89/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.08  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.89/1.08  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.89/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.08  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.89/1.08  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.89/1.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.89/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.08  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.89/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.08  thf(t76_tops_1, conjecture,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.08           ( ( v3_pre_topc @ B @ A ) <=>
% 0.89/1.08             ( ( k2_tops_1 @ A @ B ) =
% 0.89/1.08               ( k7_subset_1 @
% 0.89/1.08                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.89/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.08    (~( ![A:$i]:
% 0.89/1.08        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.08          ( ![B:$i]:
% 0.89/1.08            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.08              ( ( v3_pre_topc @ B @ A ) <=>
% 0.89/1.08                ( ( k2_tops_1 @ A @ B ) =
% 0.89/1.08                  ( k7_subset_1 @
% 0.89/1.08                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.89/1.08    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.89/1.08  thf('0', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.89/1.08        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('1', plain,
% 0.89/1.08      (~
% 0.89/1.08       (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.89/1.08       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.08      inference('split', [status(esa)], ['0'])).
% 0.89/1.08  thf('2', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('3', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.89/1.08        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('4', plain,
% 0.89/1.08      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.08      inference('split', [status(esa)], ['3'])).
% 0.89/1.08  thf('5', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(t56_tops_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( l1_pre_topc @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.08           ( ![C:$i]:
% 0.89/1.08             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.08               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.89/1.08                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.89/1.08  thf('6', plain,
% 0.89/1.08      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.89/1.08          | ~ (v3_pre_topc @ X43 @ X44)
% 0.89/1.08          | ~ (r1_tarski @ X43 @ X45)
% 0.89/1.08          | (r1_tarski @ X43 @ (k1_tops_1 @ X44 @ X45))
% 0.89/1.08          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.89/1.08          | ~ (l1_pre_topc @ X44))),
% 0.89/1.08      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.89/1.08  thf('7', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (l1_pre_topc @ sk_A)
% 0.89/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.08          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.89/1.08          | ~ (r1_tarski @ sk_B @ X0)
% 0.89/1.08          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.08      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.08  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('9', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.08          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.89/1.08          | ~ (r1_tarski @ sk_B @ X0)
% 0.89/1.08          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.08      inference('demod', [status(thm)], ['7', '8'])).
% 0.89/1.08  thf('10', plain,
% 0.89/1.08      ((![X0 : $i]:
% 0.89/1.08          (~ (r1_tarski @ sk_B @ X0)
% 0.89/1.08           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.89/1.08           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.89/1.08         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['4', '9'])).
% 0.89/1.08  thf('11', plain,
% 0.89/1.08      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.89/1.08         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['2', '10'])).
% 0.89/1.08  thf(d10_xboole_0, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.08  thf('12', plain,
% 0.89/1.08      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.89/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.08  thf('13', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.89/1.08      inference('simplify', [status(thm)], ['12'])).
% 0.89/1.08  thf('14', plain,
% 0.89/1.08      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.89/1.08         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.08      inference('demod', [status(thm)], ['11', '13'])).
% 0.89/1.08  thf('15', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(t74_tops_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( l1_pre_topc @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.08           ( ( k1_tops_1 @ A @ B ) =
% 0.89/1.08             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.08  thf('16', plain,
% 0.89/1.08      (![X48 : $i, X49 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.89/1.08          | ((k1_tops_1 @ X49 @ X48)
% 0.89/1.08              = (k7_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 0.89/1.08                 (k2_tops_1 @ X49 @ X48)))
% 0.89/1.08          | ~ (l1_pre_topc @ X49))),
% 0.89/1.08      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.89/1.08  thf('17', plain,
% 0.89/1.08      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.08        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.08            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.08               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['15', '16'])).
% 0.89/1.08  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('19', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(redefinition_k7_subset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.08       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.89/1.08  thf('20', plain,
% 0.89/1.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.89/1.08          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k4_xboole_0 @ X29 @ X31)))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.89/1.08  thf(redefinition_k6_subset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.89/1.08  thf('21', plain,
% 0.89/1.08      (![X27 : $i, X28 : $i]:
% 0.89/1.08         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.08  thf('22', plain,
% 0.89/1.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.89/1.08          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k6_subset_1 @ X29 @ X31)))),
% 0.89/1.08      inference('demod', [status(thm)], ['20', '21'])).
% 0.89/1.08  thf('23', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.89/1.08           = (k6_subset_1 @ sk_B @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['19', '22'])).
% 0.89/1.08  thf('24', plain,
% 0.89/1.08      (((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.08         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('demod', [status(thm)], ['17', '18', '23'])).
% 0.89/1.08  thf(dt_k6_subset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.89/1.08  thf('25', plain,
% 0.89/1.08      (![X25 : $i, X26 : $i]:
% 0.89/1.08         (m1_subset_1 @ (k6_subset_1 @ X25 @ X26) @ (k1_zfmisc_1 @ X25))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.89/1.08  thf(t3_subset, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.89/1.08  thf('26', plain,
% 0.89/1.08      (![X34 : $i, X35 : $i]:
% 0.89/1.08         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.89/1.08      inference('cnf', [status(esa)], [t3_subset])).
% 0.89/1.08  thf('27', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.89/1.08      inference('sup-', [status(thm)], ['25', '26'])).
% 0.89/1.08  thf('28', plain,
% 0.89/1.08      (![X13 : $i, X15 : $i]:
% 0.89/1.08         (((X13) = (X15))
% 0.89/1.08          | ~ (r1_tarski @ X15 @ X13)
% 0.89/1.08          | ~ (r1_tarski @ X13 @ X15))),
% 0.89/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.08  thf('29', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.89/1.08          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['27', '28'])).
% 0.89/1.08  thf('30', plain,
% 0.89/1.08      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.89/1.08        | ((sk_B) = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['24', '29'])).
% 0.89/1.08  thf('31', plain,
% 0.89/1.08      (((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.08         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('demod', [status(thm)], ['17', '18', '23'])).
% 0.89/1.08  thf('32', plain,
% 0.89/1.08      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.89/1.08        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('demod', [status(thm)], ['30', '31'])).
% 0.89/1.08  thf('33', plain,
% 0.89/1.08      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))
% 0.89/1.08         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['14', '32'])).
% 0.89/1.08  thf('34', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(l78_tops_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( l1_pre_topc @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.08           ( ( k2_tops_1 @ A @ B ) =
% 0.89/1.08             ( k7_subset_1 @
% 0.89/1.08               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.89/1.08               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.08  thf('35', plain,
% 0.89/1.08      (![X41 : $i, X42 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.89/1.08          | ((k2_tops_1 @ X42 @ X41)
% 0.89/1.08              = (k7_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.89/1.08                 (k2_pre_topc @ X42 @ X41) @ (k1_tops_1 @ X42 @ X41)))
% 0.89/1.08          | ~ (l1_pre_topc @ X42))),
% 0.89/1.08      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.89/1.08  thf('36', plain,
% 0.89/1.08      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.08        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['34', '35'])).
% 0.89/1.08  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('38', plain,
% 0.89/1.08      (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.89/1.08            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('demod', [status(thm)], ['36', '37'])).
% 0.89/1.08  thf('39', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.89/1.08         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['33', '38'])).
% 0.89/1.08  thf('40', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.89/1.08      inference('split', [status(esa)], ['0'])).
% 0.89/1.08  thf('41', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.89/1.08         <= (~
% 0.89/1.08             (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.89/1.08             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['39', '40'])).
% 0.89/1.08  thf('42', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.89/1.08       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.08      inference('simplify', [status(thm)], ['41'])).
% 0.89/1.08  thf('43', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.89/1.08       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.08      inference('split', [status(esa)], ['3'])).
% 0.89/1.08  thf('44', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(dt_k2_tops_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( ( l1_pre_topc @ A ) & 
% 0.89/1.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.89/1.08       ( m1_subset_1 @
% 0.89/1.08         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.89/1.08  thf('45', plain,
% 0.89/1.08      (![X37 : $i, X38 : $i]:
% 0.89/1.08         (~ (l1_pre_topc @ X37)
% 0.89/1.08          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.89/1.08          | (m1_subset_1 @ (k2_tops_1 @ X37 @ X38) @ 
% 0.89/1.08             (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.89/1.08  thf('46', plain,
% 0.89/1.08      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.89/1.08         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.08        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.08      inference('sup-', [status(thm)], ['44', '45'])).
% 0.89/1.08  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('48', plain,
% 0.89/1.08      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.89/1.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('demod', [status(thm)], ['46', '47'])).
% 0.89/1.08  thf('49', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(dt_k4_subset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.89/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.89/1.08       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.89/1.08  thf('50', plain,
% 0.89/1.08      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.89/1.08          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.89/1.08          | (m1_subset_1 @ (k4_subset_1 @ X23 @ X22 @ X24) @ 
% 0.89/1.08             (k1_zfmisc_1 @ X23)))),
% 0.89/1.08      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.89/1.08  thf('51', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.89/1.08           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.89/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['49', '50'])).
% 0.89/1.08  thf('52', plain,
% 0.89/1.08      ((m1_subset_1 @ 
% 0.89/1.08        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.89/1.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['48', '51'])).
% 0.89/1.08  thf('53', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(t65_tops_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( l1_pre_topc @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.08           ( ( k2_pre_topc @ A @ B ) =
% 0.89/1.08             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.89/1.08  thf('54', plain,
% 0.89/1.08      (![X46 : $i, X47 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 0.89/1.08          | ((k2_pre_topc @ X47 @ X46)
% 0.89/1.08              = (k4_subset_1 @ (u1_struct_0 @ X47) @ X46 @ 
% 0.89/1.08                 (k2_tops_1 @ X47 @ X46)))
% 0.89/1.08          | ~ (l1_pre_topc @ X47))),
% 0.89/1.08      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.89/1.08  thf('55', plain,
% 0.89/1.08      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.08        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.89/1.08            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.08               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['53', '54'])).
% 0.89/1.08  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('57', plain,
% 0.89/1.08      (((k2_pre_topc @ sk_A @ sk_B)
% 0.89/1.08         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.89/1.08            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('demod', [status(thm)], ['55', '56'])).
% 0.89/1.08  thf('58', plain,
% 0.89/1.08      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.89/1.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('demod', [status(thm)], ['52', '57'])).
% 0.89/1.08  thf('59', plain,
% 0.89/1.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.89/1.08          | ((k7_subset_1 @ X30 @ X29 @ X31) = (k6_subset_1 @ X29 @ X31)))),
% 0.89/1.08      inference('demod', [status(thm)], ['20', '21'])).
% 0.89/1.08  thf('60', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.89/1.08           X0) = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.08  thf('61', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.89/1.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.89/1.08      inference('split', [status(esa)], ['3'])).
% 0.89/1.08  thf('62', plain,
% 0.89/1.08      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.89/1.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.89/1.08      inference('sup+', [status(thm)], ['60', '61'])).
% 0.89/1.08  thf(d4_xboole_0, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.89/1.08       ( ![D:$i]:
% 0.89/1.08         ( ( r2_hidden @ D @ C ) <=>
% 0.89/1.08           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.89/1.08  thf('63', plain,
% 0.89/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.89/1.08         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.89/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.89/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.89/1.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.89/1.08  thf(t4_boole, axiom,
% 0.89/1.08    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.89/1.08  thf('64', plain,
% 0.89/1.08      (![X19 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.89/1.08      inference('cnf', [status(esa)], [t4_boole])).
% 0.89/1.08  thf('65', plain,
% 0.89/1.08      (![X27 : $i, X28 : $i]:
% 0.89/1.08         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.08  thf('66', plain,
% 0.89/1.08      (![X19 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.89/1.08      inference('demod', [status(thm)], ['64', '65'])).
% 0.89/1.08  thf(d5_xboole_0, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.89/1.08       ( ![D:$i]:
% 0.89/1.08         ( ( r2_hidden @ D @ C ) <=>
% 0.89/1.08           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.89/1.08  thf('67', plain,
% 0.89/1.08      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X10 @ X9)
% 0.89/1.08          | ~ (r2_hidden @ X10 @ X8)
% 0.89/1.08          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.89/1.08      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.89/1.08  thf('68', plain,
% 0.89/1.08      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X10 @ X8)
% 0.89/1.08          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.89/1.08      inference('simplify', [status(thm)], ['67'])).
% 0.89/1.08  thf('69', plain,
% 0.89/1.08      (![X27 : $i, X28 : $i]:
% 0.89/1.08         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.08  thf('70', plain,
% 0.89/1.08      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X10 @ X8)
% 0.89/1.08          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 0.89/1.08      inference('demod', [status(thm)], ['68', '69'])).
% 0.89/1.08  thf('71', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['66', '70'])).
% 0.89/1.08  thf('72', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.89/1.08      inference('condensation', [status(thm)], ['71'])).
% 0.89/1.08  thf('73', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.89/1.08          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['63', '72'])).
% 0.89/1.08  thf('74', plain,
% 0.89/1.08      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.89/1.08         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.89/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.89/1.08          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.89/1.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.89/1.08  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.89/1.08      inference('condensation', [status(thm)], ['71'])).
% 0.89/1.08  thf('76', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.89/1.08          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['74', '75'])).
% 0.89/1.08  thf('77', plain,
% 0.89/1.08      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X10 @ X8)
% 0.89/1.08          | ~ (r2_hidden @ X10 @ (k6_subset_1 @ X7 @ X8)))),
% 0.89/1.08      inference('demod', [status(thm)], ['68', '69'])).
% 0.89/1.08  thf('78', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.08         (((k1_xboole_0) = (k3_xboole_0 @ X2 @ (k6_subset_1 @ X1 @ X0)))
% 0.89/1.08          | ~ (r2_hidden @ 
% 0.89/1.08               (sk_D @ k1_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X2) @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['76', '77'])).
% 0.89/1.08  thf('79', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))
% 0.89/1.08          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['73', '78'])).
% 0.89/1.08  thf('80', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 0.89/1.08      inference('simplify', [status(thm)], ['79'])).
% 0.89/1.08  thf('81', plain,
% 0.89/1.08      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.89/1.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.89/1.08      inference('sup+', [status(thm)], ['62', '80'])).
% 0.89/1.08  thf(t100_xboole_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.89/1.08  thf('82', plain,
% 0.89/1.08      (![X16 : $i, X17 : $i]:
% 0.89/1.08         ((k4_xboole_0 @ X16 @ X17)
% 0.89/1.08           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.89/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.89/1.08  thf('83', plain,
% 0.89/1.08      (![X27 : $i, X28 : $i]:
% 0.89/1.08         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.08  thf('84', plain,
% 0.89/1.08      (![X16 : $i, X17 : $i]:
% 0.89/1.08         ((k6_subset_1 @ X16 @ X17)
% 0.89/1.08           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.89/1.08      inference('demod', [status(thm)], ['82', '83'])).
% 0.89/1.08  thf('85', plain,
% 0.89/1.08      ((((k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.89/1.08          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.89/1.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.89/1.08      inference('sup+', [status(thm)], ['81', '84'])).
% 0.89/1.08  thf('86', plain,
% 0.89/1.08      (![X19 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.89/1.08      inference('demod', [status(thm)], ['64', '65'])).
% 0.89/1.08  thf(t98_xboole_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.89/1.08  thf('87', plain,
% 0.89/1.08      (![X20 : $i, X21 : $i]:
% 0.89/1.08         ((k2_xboole_0 @ X20 @ X21)
% 0.89/1.08           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.89/1.08      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.89/1.08  thf('88', plain,
% 0.89/1.08      (![X27 : $i, X28 : $i]:
% 0.89/1.08         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.08  thf('89', plain,
% 0.89/1.08      (![X20 : $i, X21 : $i]:
% 0.89/1.08         ((k2_xboole_0 @ X20 @ X21)
% 0.89/1.08           = (k5_xboole_0 @ X20 @ (k6_subset_1 @ X21 @ X20)))),
% 0.89/1.08      inference('demod', [status(thm)], ['87', '88'])).
% 0.89/1.08  thf('90', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.08      inference('sup+', [status(thm)], ['86', '89'])).
% 0.89/1.08  thf(t1_boole, axiom,
% 0.89/1.08    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.08  thf('91', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.89/1.08      inference('cnf', [status(esa)], [t1_boole])).
% 0.89/1.08  thf('92', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.89/1.08      inference('sup+', [status(thm)], ['90', '91'])).
% 0.89/1.08  thf('93', plain,
% 0.89/1.08      ((((k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.89/1.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.89/1.08      inference('demod', [status(thm)], ['85', '92'])).
% 0.89/1.08  thf('94', plain,
% 0.89/1.08      (((k1_tops_1 @ sk_A @ sk_B)
% 0.89/1.08         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('demod', [status(thm)], ['17', '18', '23'])).
% 0.89/1.08  thf('95', plain,
% 0.89/1.08      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.89/1.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.89/1.08      inference('sup+', [status(thm)], ['93', '94'])).
% 0.89/1.08  thf('96', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(fc9_tops_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.89/1.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.89/1.08       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.89/1.08  thf('97', plain,
% 0.89/1.08      (![X39 : $i, X40 : $i]:
% 0.89/1.08         (~ (l1_pre_topc @ X39)
% 0.89/1.08          | ~ (v2_pre_topc @ X39)
% 0.89/1.08          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.89/1.08          | (v3_pre_topc @ (k1_tops_1 @ X39 @ X40) @ X39))),
% 0.89/1.08      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.89/1.08  thf('98', plain,
% 0.89/1.08      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.89/1.08        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.08        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.08      inference('sup-', [status(thm)], ['96', '97'])).
% 0.89/1.08  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('101', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.89/1.08      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.89/1.08  thf('102', plain,
% 0.89/1.08      (((v3_pre_topc @ sk_B @ sk_A))
% 0.89/1.08         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.89/1.08      inference('sup+', [status(thm)], ['95', '101'])).
% 0.89/1.08  thf('103', plain,
% 0.89/1.08      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.89/1.08      inference('split', [status(esa)], ['0'])).
% 0.89/1.08  thf('104', plain,
% 0.89/1.08      (~
% 0.89/1.08       (((k2_tops_1 @ sk_A @ sk_B)
% 0.89/1.08          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.89/1.08             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.89/1.08       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.89/1.08      inference('sup-', [status(thm)], ['102', '103'])).
% 0.89/1.08  thf('105', plain, ($false),
% 0.89/1.08      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '104'])).
% 0.89/1.08  
% 0.89/1.08  % SZS output end Refutation
% 0.89/1.08  
% 0.89/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
