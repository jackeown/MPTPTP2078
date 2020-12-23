%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.561WUuHoUq

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:41 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 340 expanded)
%              Number of leaves         :   50 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          : 1638 (3449 expanded)
%              Number of equality atoms :  130 ( 259 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k1_tops_1 @ X64 @ X63 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k4_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k7_subset_1 @ X44 @ X43 @ X45 )
        = ( k6_subset_1 @ X43 @ X45 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('16',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X62 @ X61 ) @ X61 )
      | ~ ( v4_pre_topc @ X61 @ X62 )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('23',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X37 @ ( k3_subset_1 @ X37 @ X36 ) )
        = X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('24',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k6_subset_1 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','29','32'])).

thf('34',plain,
    ( ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['12','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_pre_topc @ X60 @ X59 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('53',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('57',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('58',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('59',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('63',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('64',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('65',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('66',plain,(
    ! [X2: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X2 @ k1_xboole_0 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('70',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('71',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('72',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k6_subset_1 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','72'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('76',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('79',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('80',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k6_subset_1 @ X11 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','81'])).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k6_subset_1 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('84',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('85',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('86',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('87',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k5_xboole_0 @ X23 @ ( k6_subset_1 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('90',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','91'])).

thf('93',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('94',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('99',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('100',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('102',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['92','97','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('112',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X8 @ X9 ) @ X8 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('113',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('114',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('115',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k6_subset_1 @ X41 @ X42 )
      = ( k4_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('116',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['111','117'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('119',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','120'])).

thf('122',plain,(
    ! [X50: $i,X52: $i] :
      ( ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X52 ) )
      | ~ ( r1_tarski @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('125',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k2_xboole_0 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('126',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('127',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X39 ) )
      | ( ( k4_subset_1 @ X39 @ X38 @ X40 )
        = ( k3_tarski @ ( k2_tarski @ X38 @ X40 ) ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) )
      = X6 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['107','131'])).

thf('133',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['45','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('135',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( v2_pre_topc @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X55 @ X56 ) @ X55 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('136',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['133','139'])).

thf('141',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.561WUuHoUq
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.36/1.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.36/1.54  % Solved by: fo/fo7.sh
% 1.36/1.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.54  % done 3787 iterations in 1.087s
% 1.36/1.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.36/1.54  % SZS output start Refutation
% 1.36/1.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.36/1.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.36/1.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.36/1.54  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.36/1.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.36/1.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.36/1.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.36/1.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.36/1.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.36/1.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.36/1.54  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.36/1.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.36/1.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.36/1.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.36/1.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.36/1.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.36/1.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.36/1.54  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.36/1.54  thf(t77_tops_1, conjecture,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.36/1.54       ( ![B:$i]:
% 1.36/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.36/1.54           ( ( v4_pre_topc @ B @ A ) <=>
% 1.36/1.54             ( ( k2_tops_1 @ A @ B ) =
% 1.36/1.54               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.36/1.54  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.54    (~( ![A:$i]:
% 1.36/1.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.36/1.54          ( ![B:$i]:
% 1.36/1.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.36/1.54              ( ( v4_pre_topc @ B @ A ) <=>
% 1.36/1.54                ( ( k2_tops_1 @ A @ B ) =
% 1.36/1.54                  ( k7_subset_1 @
% 1.36/1.54                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.36/1.54    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.36/1.54  thf('0', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54              (k1_tops_1 @ sk_A @ sk_B)))
% 1.36/1.54        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('1', plain,
% 1.36/1.54      (~
% 1.36/1.54       (((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.36/1.54       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.36/1.54      inference('split', [status(esa)], ['0'])).
% 1.36/1.54  thf('2', plain,
% 1.36/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(t74_tops_1, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( l1_pre_topc @ A ) =>
% 1.36/1.54       ( ![B:$i]:
% 1.36/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.36/1.54           ( ( k1_tops_1 @ A @ B ) =
% 1.36/1.54             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.36/1.54  thf('3', plain,
% 1.36/1.54      (![X63 : $i, X64 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 1.36/1.54          | ((k1_tops_1 @ X64 @ X63)
% 1.36/1.54              = (k7_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 1.36/1.54                 (k2_tops_1 @ X64 @ X63)))
% 1.36/1.54          | ~ (l1_pre_topc @ X64))),
% 1.36/1.54      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.36/1.54  thf('4', plain,
% 1.36/1.54      ((~ (l1_pre_topc @ sk_A)
% 1.36/1.54        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.36/1.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['2', '3'])).
% 1.36/1.54  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('6', plain,
% 1.36/1.54      (((k1_tops_1 @ sk_A @ sk_B)
% 1.36/1.54         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.36/1.54      inference('demod', [status(thm)], ['4', '5'])).
% 1.36/1.54  thf('7', plain,
% 1.36/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(redefinition_k7_subset_1, axiom,
% 1.36/1.54    (![A:$i,B:$i,C:$i]:
% 1.36/1.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.36/1.54       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.36/1.54  thf('8', plain,
% 1.36/1.54      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 1.36/1.54          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k4_xboole_0 @ X43 @ X45)))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.36/1.54  thf(redefinition_k6_subset_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.36/1.54  thf('9', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('10', plain,
% 1.36/1.54      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 1.36/1.54          | ((k7_subset_1 @ X44 @ X43 @ X45) = (k6_subset_1 @ X43 @ X45)))),
% 1.36/1.54      inference('demod', [status(thm)], ['8', '9'])).
% 1.36/1.54  thf('11', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.36/1.54           = (k6_subset_1 @ sk_B @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['7', '10'])).
% 1.36/1.54  thf('12', plain,
% 1.36/1.54      (((k1_tops_1 @ sk_A @ sk_B)
% 1.36/1.54         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.36/1.54      inference('demod', [status(thm)], ['6', '11'])).
% 1.36/1.54  thf('13', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54             (k1_tops_1 @ sk_A @ sk_B)))
% 1.36/1.54        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('14', plain,
% 1.36/1.54      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('split', [status(esa)], ['13'])).
% 1.36/1.54  thf('15', plain,
% 1.36/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(t69_tops_1, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( l1_pre_topc @ A ) =>
% 1.36/1.54       ( ![B:$i]:
% 1.36/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.36/1.54           ( ( v4_pre_topc @ B @ A ) =>
% 1.36/1.54             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.36/1.54  thf('16', plain,
% 1.36/1.54      (![X61 : $i, X62 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 1.36/1.54          | (r1_tarski @ (k2_tops_1 @ X62 @ X61) @ X61)
% 1.36/1.54          | ~ (v4_pre_topc @ X61 @ X62)
% 1.36/1.54          | ~ (l1_pre_topc @ X62))),
% 1.36/1.54      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.36/1.54  thf('17', plain,
% 1.36/1.54      ((~ (l1_pre_topc @ sk_A)
% 1.36/1.54        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.36/1.54        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.36/1.54      inference('sup-', [status(thm)], ['15', '16'])).
% 1.36/1.54  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('19', plain,
% 1.36/1.54      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.36/1.54        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.36/1.54      inference('demod', [status(thm)], ['17', '18'])).
% 1.36/1.54  thf('20', plain,
% 1.36/1.54      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.36/1.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['14', '19'])).
% 1.36/1.54  thf(t3_subset, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.36/1.54  thf('21', plain,
% 1.36/1.54      (![X50 : $i, X52 : $i]:
% 1.36/1.54         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 1.36/1.54      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.54  thf('22', plain,
% 1.36/1.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.36/1.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['20', '21'])).
% 1.36/1.54  thf(involutiveness_k3_subset_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.36/1.54       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.36/1.54  thf('23', plain,
% 1.36/1.54      (![X36 : $i, X37 : $i]:
% 1.36/1.54         (((k3_subset_1 @ X37 @ (k3_subset_1 @ X37 @ X36)) = (X36))
% 1.36/1.54          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 1.36/1.54      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.36/1.54  thf('24', plain,
% 1.36/1.54      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.36/1.54          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.36/1.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['22', '23'])).
% 1.36/1.54  thf('25', plain,
% 1.36/1.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 1.36/1.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['20', '21'])).
% 1.36/1.54  thf(d5_subset_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.36/1.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.36/1.54  thf('26', plain,
% 1.36/1.54      (![X30 : $i, X31 : $i]:
% 1.36/1.54         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 1.36/1.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 1.36/1.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.36/1.54  thf('27', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('28', plain,
% 1.36/1.54      (![X30 : $i, X31 : $i]:
% 1.36/1.54         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 1.36/1.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 1.36/1.54      inference('demod', [status(thm)], ['26', '27'])).
% 1.36/1.54  thf('29', plain,
% 1.36/1.54      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.36/1.54          = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.36/1.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['25', '28'])).
% 1.36/1.54  thf(dt_k6_subset_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.36/1.54  thf('30', plain,
% 1.36/1.54      (![X34 : $i, X35 : $i]:
% 1.36/1.54         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 1.36/1.54      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.36/1.54  thf('31', plain,
% 1.36/1.54      (![X30 : $i, X31 : $i]:
% 1.36/1.54         (((k3_subset_1 @ X30 @ X31) = (k6_subset_1 @ X30 @ X31))
% 1.36/1.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 1.36/1.54      inference('demod', [status(thm)], ['26', '27'])).
% 1.36/1.54  thf('32', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 1.36/1.54           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['30', '31'])).
% 1.36/1.54  thf('33', plain,
% 1.36/1.54      ((((k6_subset_1 @ sk_B @ (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.36/1.54          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.36/1.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('demod', [status(thm)], ['24', '29', '32'])).
% 1.36/1.54  thf('34', plain,
% 1.36/1.54      ((((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.36/1.54          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.36/1.54         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('sup+', [status(thm)], ['12', '33'])).
% 1.36/1.54  thf('35', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.36/1.54           = (k6_subset_1 @ sk_B @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['7', '10'])).
% 1.36/1.54  thf('36', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54              (k1_tops_1 @ sk_A @ sk_B))))
% 1.36/1.54         <= (~
% 1.36/1.54             (((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('split', [status(esa)], ['0'])).
% 1.36/1.54  thf('37', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.36/1.54         <= (~
% 1.36/1.54             (((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['35', '36'])).
% 1.36/1.54  thf('38', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.36/1.54         <= (~
% 1.36/1.54             (((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))) & 
% 1.36/1.54             ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['34', '37'])).
% 1.36/1.54  thf('39', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.36/1.54       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.36/1.54      inference('simplify', [status(thm)], ['38'])).
% 1.36/1.54  thf('40', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.36/1.54       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.36/1.54      inference('split', [status(esa)], ['13'])).
% 1.36/1.54  thf('41', plain,
% 1.36/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(t65_tops_1, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( l1_pre_topc @ A ) =>
% 1.36/1.54       ( ![B:$i]:
% 1.36/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.36/1.54           ( ( k2_pre_topc @ A @ B ) =
% 1.36/1.54             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.36/1.54  thf('42', plain,
% 1.36/1.54      (![X59 : $i, X60 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 1.36/1.54          | ((k2_pre_topc @ X60 @ X59)
% 1.36/1.54              = (k4_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 1.36/1.54                 (k2_tops_1 @ X60 @ X59)))
% 1.36/1.54          | ~ (l1_pre_topc @ X60))),
% 1.36/1.54      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.36/1.54  thf('43', plain,
% 1.36/1.54      ((~ (l1_pre_topc @ sk_A)
% 1.36/1.54        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.36/1.54            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['41', '42'])).
% 1.36/1.54  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('45', plain,
% 1.36/1.54      (((k2_pre_topc @ sk_A @ sk_B)
% 1.36/1.54         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.36/1.54      inference('demod', [status(thm)], ['43', '44'])).
% 1.36/1.54  thf('46', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.36/1.54           = (k6_subset_1 @ sk_B @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['7', '10'])).
% 1.36/1.54  thf('47', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54             (k1_tops_1 @ sk_A @ sk_B))))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('split', [status(esa)], ['13'])).
% 1.36/1.54  thf('48', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup+', [status(thm)], ['46', '47'])).
% 1.36/1.54  thf(t36_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.36/1.54  thf('49', plain,
% 1.36/1.54      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.36/1.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.36/1.54  thf('50', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('51', plain,
% 1.36/1.54      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 1.36/1.54      inference('demod', [status(thm)], ['49', '50'])).
% 1.36/1.54  thf('52', plain,
% 1.36/1.54      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup+', [status(thm)], ['48', '51'])).
% 1.36/1.54  thf(t1_boole, axiom,
% 1.36/1.54    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.36/1.54  thf('53', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.36/1.54      inference('cnf', [status(esa)], [t1_boole])).
% 1.36/1.54  thf(l51_zfmisc_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.36/1.54  thf('54', plain,
% 1.36/1.54      (![X27 : $i, X28 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 1.36/1.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.36/1.54  thf('55', plain,
% 1.36/1.54      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 1.36/1.54      inference('demod', [status(thm)], ['53', '54'])).
% 1.36/1.54  thf(t43_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i,C:$i]:
% 1.36/1.54     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.36/1.54       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.36/1.54  thf('56', plain,
% 1.36/1.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.36/1.54         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.36/1.54          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.36/1.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.36/1.54  thf('57', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('58', plain,
% 1.36/1.54      (![X27 : $i, X28 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 1.36/1.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.36/1.54  thf('59', plain,
% 1.36/1.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.36/1.54         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 1.36/1.54          | ~ (r1_tarski @ X13 @ (k3_tarski @ (k2_tarski @ X14 @ X15))))),
% 1.36/1.54      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.36/1.54  thf('60', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (r1_tarski @ X1 @ X0)
% 1.36/1.54          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ k1_xboole_0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['55', '59'])).
% 1.36/1.54  thf('61', plain,
% 1.36/1.54      (((r1_tarski @ (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.36/1.54         k1_xboole_0))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['52', '60'])).
% 1.36/1.54  thf(t22_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.36/1.54  thf('62', plain,
% 1.36/1.54      (![X6 : $i, X7 : $i]:
% 1.36/1.54         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 1.36/1.54      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.36/1.54  thf('63', plain,
% 1.36/1.54      (![X27 : $i, X28 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 1.36/1.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.36/1.54  thf('64', plain,
% 1.36/1.54      (![X6 : $i, X7 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 1.36/1.54      inference('demod', [status(thm)], ['62', '63'])).
% 1.36/1.54  thf(commutativity_k2_tarski, axiom,
% 1.36/1.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.36/1.54  thf('65', plain,
% 1.36/1.54      (![X25 : $i, X26 : $i]:
% 1.36/1.54         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 1.36/1.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.36/1.54  thf('66', plain,
% 1.36/1.54      (![X2 : $i]: ((k3_tarski @ (k2_tarski @ X2 @ k1_xboole_0)) = (X2))),
% 1.36/1.54      inference('demod', [status(thm)], ['53', '54'])).
% 1.36/1.54  thf('67', plain,
% 1.36/1.54      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['65', '66'])).
% 1.36/1.54  thf('68', plain,
% 1.36/1.54      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['64', '67'])).
% 1.36/1.54  thf(t47_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.36/1.54  thf('69', plain,
% 1.36/1.54      (![X19 : $i, X20 : $i]:
% 1.36/1.54         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 1.36/1.54           = (k4_xboole_0 @ X19 @ X20))),
% 1.36/1.54      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.36/1.54  thf('70', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('71', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('72', plain,
% 1.36/1.54      (![X19 : $i, X20 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 1.36/1.54           = (k6_subset_1 @ X19 @ X20))),
% 1.36/1.54      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.36/1.54  thf('73', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((k6_subset_1 @ k1_xboole_0 @ k1_xboole_0)
% 1.36/1.54           = (k6_subset_1 @ k1_xboole_0 @ X0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['68', '72'])).
% 1.36/1.54  thf(t3_boole, axiom,
% 1.36/1.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.36/1.54  thf('74', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.36/1.54      inference('cnf', [status(esa)], [t3_boole])).
% 1.36/1.54  thf('75', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('76', plain, (![X12 : $i]: ((k6_subset_1 @ X12 @ k1_xboole_0) = (X12))),
% 1.36/1.54      inference('demod', [status(thm)], ['74', '75'])).
% 1.36/1.54  thf('77', plain,
% 1.36/1.54      (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ k1_xboole_0 @ X0))),
% 1.36/1.54      inference('demod', [status(thm)], ['73', '76'])).
% 1.36/1.54  thf(t38_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.36/1.54       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.36/1.54  thf('78', plain,
% 1.36/1.54      (![X10 : $i, X11 : $i]:
% 1.36/1.54         (((X10) = (k1_xboole_0))
% 1.36/1.54          | ~ (r1_tarski @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 1.36/1.54      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.36/1.54  thf('79', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('80', plain,
% 1.36/1.54      (![X10 : $i, X11 : $i]:
% 1.36/1.54         (((X10) = (k1_xboole_0))
% 1.36/1.54          | ~ (r1_tarski @ X10 @ (k6_subset_1 @ X11 @ X10)))),
% 1.36/1.54      inference('demod', [status(thm)], ['78', '79'])).
% 1.36/1.54  thf('81', plain,
% 1.36/1.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['77', '80'])).
% 1.36/1.54  thf('82', plain,
% 1.36/1.54      ((((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['61', '81'])).
% 1.36/1.54  thf('83', plain,
% 1.36/1.54      (![X19 : $i, X20 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 1.36/1.54           = (k6_subset_1 @ X19 @ X20))),
% 1.36/1.54      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.36/1.54  thf(t98_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.36/1.54  thf('84', plain,
% 1.36/1.54      (![X23 : $i, X24 : $i]:
% 1.36/1.54         ((k2_xboole_0 @ X23 @ X24)
% 1.36/1.54           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 1.36/1.54      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.36/1.54  thf('85', plain,
% 1.36/1.54      (![X27 : $i, X28 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 1.36/1.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.36/1.54  thf('86', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('87', plain,
% 1.36/1.54      (![X23 : $i, X24 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X23 @ X24))
% 1.36/1.54           = (k5_xboole_0 @ X23 @ (k6_subset_1 @ X24 @ X23)))),
% 1.36/1.54      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.36/1.54  thf('88', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 1.36/1.54           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 1.36/1.54      inference('sup+', [status(thm)], ['83', '87'])).
% 1.36/1.54  thf('89', plain,
% 1.36/1.54      (![X25 : $i, X26 : $i]:
% 1.36/1.54         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 1.36/1.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.36/1.54  thf('90', plain,
% 1.36/1.54      (![X6 : $i, X7 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 1.36/1.54      inference('demod', [status(thm)], ['62', '63'])).
% 1.36/1.54  thf('91', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((X1)
% 1.36/1.54           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.36/1.54  thf('92', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k5_xboole_0 @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.36/1.54             k1_xboole_0)))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup+', [status(thm)], ['82', '91'])).
% 1.36/1.54  thf('93', plain,
% 1.36/1.54      (![X25 : $i, X26 : $i]:
% 1.36/1.54         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 1.36/1.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.36/1.54  thf(t12_setfam_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.36/1.54  thf('94', plain,
% 1.36/1.54      (![X48 : $i, X49 : $i]:
% 1.36/1.54         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 1.36/1.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.36/1.54  thf('95', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['93', '94'])).
% 1.36/1.54  thf('96', plain,
% 1.36/1.54      (![X48 : $i, X49 : $i]:
% 1.36/1.54         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 1.36/1.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.36/1.54  thf('97', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['95', '96'])).
% 1.36/1.54  thf('98', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['95', '96'])).
% 1.36/1.54  thf('99', plain,
% 1.36/1.54      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['64', '67'])).
% 1.36/1.54  thf('100', plain,
% 1.36/1.54      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['98', '99'])).
% 1.36/1.54  thf(t100_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.36/1.54  thf('101', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((k4_xboole_0 @ X0 @ X1)
% 1.36/1.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.36/1.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.36/1.54  thf('102', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('103', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X0 @ X1)
% 1.36/1.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.36/1.54      inference('demod', [status(thm)], ['101', '102'])).
% 1.36/1.54  thf('104', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['100', '103'])).
% 1.36/1.54  thf('105', plain, (![X12 : $i]: ((k6_subset_1 @ X12 @ k1_xboole_0) = (X12))),
% 1.36/1.54      inference('demod', [status(thm)], ['74', '75'])).
% 1.36/1.54  thf('106', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['104', '105'])).
% 1.36/1.54  thf('107', plain,
% 1.36/1.54      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('demod', [status(thm)], ['92', '97', '106'])).
% 1.36/1.54  thf('108', plain,
% 1.36/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('109', plain,
% 1.36/1.54      (![X50 : $i, X51 : $i]:
% 1.36/1.54         ((r1_tarski @ X50 @ X51) | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X51)))),
% 1.36/1.54      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.54  thf('110', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.36/1.54      inference('sup-', [status(thm)], ['108', '109'])).
% 1.36/1.54  thf('111', plain,
% 1.36/1.54      (![X6 : $i, X7 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 1.36/1.54      inference('demod', [status(thm)], ['62', '63'])).
% 1.36/1.54  thf('112', plain,
% 1.36/1.54      (![X8 : $i, X9 : $i]: (r1_tarski @ (k6_subset_1 @ X8 @ X9) @ X8)),
% 1.36/1.54      inference('demod', [status(thm)], ['49', '50'])).
% 1.36/1.54  thf(t44_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i,C:$i]:
% 1.36/1.54     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.36/1.54       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.36/1.54  thf('113', plain,
% 1.36/1.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.36/1.54         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.36/1.54          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 1.36/1.54      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.36/1.54  thf('114', plain,
% 1.36/1.54      (![X27 : $i, X28 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 1.36/1.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.36/1.54  thf('115', plain,
% 1.36/1.54      (![X41 : $i, X42 : $i]:
% 1.36/1.54         ((k6_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.36/1.54  thf('116', plain,
% 1.36/1.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.36/1.54         ((r1_tarski @ X16 @ (k3_tarski @ (k2_tarski @ X17 @ X18)))
% 1.36/1.54          | ~ (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18))),
% 1.36/1.54      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.36/1.54  thf('117', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['112', '116'])).
% 1.36/1.54  thf('118', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.36/1.54      inference('sup+', [status(thm)], ['111', '117'])).
% 1.36/1.54  thf(t1_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i,C:$i]:
% 1.36/1.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.36/1.54       ( r1_tarski @ A @ C ) ))).
% 1.36/1.54  thf('119', plain,
% 1.36/1.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.36/1.54         (~ (r1_tarski @ X3 @ X4)
% 1.36/1.54          | ~ (r1_tarski @ X4 @ X5)
% 1.36/1.54          | (r1_tarski @ X3 @ X5))),
% 1.36/1.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.36/1.54  thf('120', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.54         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 1.36/1.54      inference('sup-', [status(thm)], ['118', '119'])).
% 1.36/1.54  thf('121', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.36/1.54      inference('sup-', [status(thm)], ['110', '120'])).
% 1.36/1.54  thf('122', plain,
% 1.36/1.54      (![X50 : $i, X52 : $i]:
% 1.36/1.54         ((m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X52)) | ~ (r1_tarski @ X50 @ X52))),
% 1.36/1.54      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.54  thf('123', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 1.36/1.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['121', '122'])).
% 1.36/1.54  thf('124', plain,
% 1.36/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(redefinition_k4_subset_1, axiom,
% 1.36/1.54    (![A:$i,B:$i,C:$i]:
% 1.36/1.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.36/1.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.36/1.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.36/1.54  thf('125', plain,
% 1.36/1.54      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.36/1.54          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 1.36/1.54          | ((k4_subset_1 @ X39 @ X38 @ X40) = (k2_xboole_0 @ X38 @ X40)))),
% 1.36/1.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.36/1.54  thf('126', plain,
% 1.36/1.54      (![X27 : $i, X28 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 1.36/1.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.36/1.54  thf('127', plain,
% 1.36/1.54      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 1.36/1.54          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X39))
% 1.36/1.54          | ((k4_subset_1 @ X39 @ X38 @ X40)
% 1.36/1.54              = (k3_tarski @ (k2_tarski @ X38 @ X40))))),
% 1.36/1.54      inference('demod', [status(thm)], ['125', '126'])).
% 1.36/1.54  thf('128', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.36/1.54            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 1.36/1.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['124', '127'])).
% 1.36/1.54  thf('129', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54           (k3_xboole_0 @ sk_B @ X0))
% 1.36/1.54           = (k3_tarski @ (k2_tarski @ sk_B @ (k3_xboole_0 @ sk_B @ X0))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['123', '128'])).
% 1.36/1.54  thf('130', plain,
% 1.36/1.54      (![X6 : $i, X7 : $i]:
% 1.36/1.54         ((k3_tarski @ (k2_tarski @ X6 @ (k3_xboole_0 @ X6 @ X7))) = (X6))),
% 1.36/1.54      inference('demod', [status(thm)], ['62', '63'])).
% 1.36/1.54  thf('131', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54           (k3_xboole_0 @ sk_B @ X0)) = (sk_B))),
% 1.36/1.54      inference('demod', [status(thm)], ['129', '130'])).
% 1.36/1.54  thf('132', plain,
% 1.36/1.54      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.36/1.54          = (sk_B)))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup+', [status(thm)], ['107', '131'])).
% 1.36/1.54  thf('133', plain,
% 1.36/1.54      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup+', [status(thm)], ['45', '132'])).
% 1.36/1.54  thf('134', plain,
% 1.36/1.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(fc1_tops_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.36/1.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.36/1.54       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.36/1.54  thf('135', plain,
% 1.36/1.54      (![X55 : $i, X56 : $i]:
% 1.36/1.54         (~ (l1_pre_topc @ X55)
% 1.36/1.54          | ~ (v2_pre_topc @ X55)
% 1.36/1.54          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 1.36/1.54          | (v4_pre_topc @ (k2_pre_topc @ X55 @ X56) @ X55))),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.36/1.54  thf('136', plain,
% 1.36/1.54      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.36/1.54        | ~ (v2_pre_topc @ sk_A)
% 1.36/1.54        | ~ (l1_pre_topc @ sk_A))),
% 1.36/1.54      inference('sup-', [status(thm)], ['134', '135'])).
% 1.36/1.54  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('139', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.36/1.54      inference('demod', [status(thm)], ['136', '137', '138'])).
% 1.36/1.54  thf('140', plain,
% 1.36/1.54      (((v4_pre_topc @ sk_B @ sk_A))
% 1.36/1.54         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.36/1.54      inference('sup+', [status(thm)], ['133', '139'])).
% 1.36/1.54  thf('141', plain,
% 1.36/1.54      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.36/1.54      inference('split', [status(esa)], ['0'])).
% 1.36/1.54  thf('142', plain,
% 1.36/1.54      (~
% 1.36/1.54       (((k2_tops_1 @ sk_A @ sk_B)
% 1.36/1.54          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.36/1.54             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.36/1.54       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.36/1.54      inference('sup-', [status(thm)], ['140', '141'])).
% 1.36/1.54  thf('143', plain, ($false),
% 1.36/1.54      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '142'])).
% 1.36/1.54  
% 1.36/1.54  % SZS output end Refutation
% 1.36/1.54  
% 1.36/1.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
