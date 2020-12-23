%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eTEAsvrEbj

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:20 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 179 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  848 (2006 expanded)
%              Number of equality atoms :   52 (  99 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t75_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
              = ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k2_tops_1 @ X39 @ X38 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_pre_topc @ X39 @ X38 ) @ ( k1_tops_1 @ X39 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v4_pre_topc @ X32 @ X33 )
      | ( ( k2_pre_topc @ X33 @ X32 )
        = X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X36 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('20',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k1_tops_1 @ X41 @ ( k2_tops_1 @ X41 @ ( k2_tops_1 @ X41 @ X40 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','42','43'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X27: $i,X29: $i] :
      ( ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('62',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','65'])).

thf('67',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','24','30','33','66'])).

thf('68',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eTEAsvrEbj
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.10/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.10/1.31  % Solved by: fo/fo7.sh
% 1.10/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.31  % done 2424 iterations in 0.864s
% 1.10/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.10/1.31  % SZS output start Refutation
% 1.10/1.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.10/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.10/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.10/1.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.10/1.31  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.10/1.31  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.10/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.10/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.10/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.10/1.31  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.10/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.10/1.31  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.10/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.10/1.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.10/1.31  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.10/1.31  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.10/1.31  thf(t75_tops_1, conjecture,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.10/1.31             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.10/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.31    (~( ![A:$i]:
% 1.10/1.31        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.10/1.31          ( ![B:$i]:
% 1.10/1.31            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.10/1.31                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 1.10/1.31    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 1.10/1.31  thf('0', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(dt_k2_tops_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( l1_pre_topc @ A ) & 
% 1.10/1.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.10/1.31       ( m1_subset_1 @
% 1.10/1.31         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.10/1.31  thf('1', plain,
% 1.10/1.31      (![X34 : $i, X35 : $i]:
% 1.10/1.31         (~ (l1_pre_topc @ X34)
% 1.10/1.31          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.10/1.31          | (m1_subset_1 @ (k2_tops_1 @ X34 @ X35) @ 
% 1.10/1.31             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.10/1.31  thf('2', plain,
% 1.10/1.31      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.10/1.31        | ~ (l1_pre_topc @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['0', '1'])).
% 1.10/1.31  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('4', plain,
% 1.10/1.31      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['2', '3'])).
% 1.10/1.31  thf('5', plain,
% 1.10/1.31      (![X34 : $i, X35 : $i]:
% 1.10/1.31         (~ (l1_pre_topc @ X34)
% 1.10/1.31          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.10/1.31          | (m1_subset_1 @ (k2_tops_1 @ X34 @ X35) @ 
% 1.10/1.31             (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 1.10/1.31      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.10/1.31  thf('6', plain,
% 1.10/1.31      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.10/1.31         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.10/1.31        | ~ (l1_pre_topc @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['4', '5'])).
% 1.10/1.31  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('8', plain,
% 1.10/1.31      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf(l78_tops_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( l1_pre_topc @ A ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( k2_tops_1 @ A @ B ) =
% 1.10/1.31             ( k7_subset_1 @
% 1.10/1.31               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.10/1.31               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.10/1.31  thf('9', plain,
% 1.10/1.31      (![X38 : $i, X39 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.10/1.31          | ((k2_tops_1 @ X39 @ X38)
% 1.10/1.31              = (k7_subset_1 @ (u1_struct_0 @ X39) @ 
% 1.10/1.31                 (k2_pre_topc @ X39 @ X38) @ (k1_tops_1 @ X39 @ X38)))
% 1.10/1.31          | ~ (l1_pre_topc @ X39))),
% 1.10/1.31      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.10/1.31  thf('10', plain,
% 1.10/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.10/1.31        | ((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.10/1.31               (k2_pre_topc @ sk_A @ 
% 1.10/1.31                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.10/1.31               (k1_tops_1 @ sk_A @ 
% 1.10/1.31                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['8', '9'])).
% 1.10/1.31  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('12', plain,
% 1.10/1.31      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.10/1.31            (k2_pre_topc @ sk_A @ 
% 1.10/1.31             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.10/1.31            (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 1.10/1.31      inference('demod', [status(thm)], ['10', '11'])).
% 1.10/1.31  thf('13', plain,
% 1.10/1.31      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf(t52_pre_topc, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( l1_pre_topc @ A ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.10/1.31             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.10/1.31               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.10/1.31  thf('14', plain,
% 1.10/1.31      (![X32 : $i, X33 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.10/1.31          | ~ (v4_pre_topc @ X32 @ X33)
% 1.10/1.31          | ((k2_pre_topc @ X33 @ X32) = (X32))
% 1.10/1.31          | ~ (l1_pre_topc @ X33))),
% 1.10/1.31      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.10/1.31  thf('15', plain,
% 1.10/1.31      ((~ (l1_pre_topc @ sk_A)
% 1.10/1.31        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.10/1.31             sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['13', '14'])).
% 1.10/1.31  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('17', plain,
% 1.10/1.31      ((((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31          = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.10/1.31             sk_A))),
% 1.10/1.31      inference('demod', [status(thm)], ['15', '16'])).
% 1.10/1.31  thf('18', plain,
% 1.10/1.31      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['2', '3'])).
% 1.10/1.31  thf(fc11_tops_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.10/1.31         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.10/1.31       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 1.10/1.31  thf('19', plain,
% 1.10/1.31      (![X36 : $i, X37 : $i]:
% 1.10/1.31         (~ (l1_pre_topc @ X36)
% 1.10/1.31          | ~ (v2_pre_topc @ X36)
% 1.10/1.31          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.10/1.31          | (v4_pre_topc @ (k2_tops_1 @ X36 @ X37) @ X36))),
% 1.10/1.31      inference('cnf', [status(esa)], [fc11_tops_1])).
% 1.10/1.31  thf('20', plain,
% 1.10/1.31      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 1.10/1.31        | ~ (v2_pre_topc @ sk_A)
% 1.10/1.31        | ~ (l1_pre_topc @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['18', '19'])).
% 1.10/1.31  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('23', plain,
% 1.10/1.31      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 1.10/1.31      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.10/1.31  thf('24', plain,
% 1.10/1.31      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.10/1.31      inference('demod', [status(thm)], ['17', '23'])).
% 1.10/1.31  thf('25', plain,
% 1.10/1.31      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(l80_tops_1, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.10/1.31             ( k1_xboole_0 ) ) ) ) ))).
% 1.10/1.31  thf('26', plain,
% 1.10/1.31      (![X40 : $i, X41 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 1.10/1.31          | ((k1_tops_1 @ X41 @ (k2_tops_1 @ X41 @ (k2_tops_1 @ X41 @ X40)))
% 1.10/1.31              = (k1_xboole_0))
% 1.10/1.31          | ~ (l1_pre_topc @ X41)
% 1.10/1.31          | ~ (v2_pre_topc @ X41))),
% 1.10/1.31      inference('cnf', [status(esa)], [l80_tops_1])).
% 1.10/1.31  thf('27', plain,
% 1.10/1.31      ((~ (v2_pre_topc @ sk_A)
% 1.10/1.31        | ~ (l1_pre_topc @ sk_A)
% 1.10/1.31        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31            = (k1_xboole_0)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['25', '26'])).
% 1.10/1.31  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('30', plain,
% 1.10/1.31      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31         = (k1_xboole_0))),
% 1.10/1.31      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.10/1.31  thf('31', plain,
% 1.10/1.31      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('demod', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf(redefinition_k7_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.31       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.10/1.31  thf('32', plain,
% 1.10/1.31      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 1.10/1.31          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 1.10/1.31      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.10/1.31  thf('33', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.10/1.31           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 1.10/1.31           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['31', '32'])).
% 1.10/1.31  thf(t46_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.10/1.31  thf('34', plain,
% 1.10/1.31      (![X16 : $i, X17 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 1.10/1.31      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.10/1.31  thf(t41_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.10/1.31       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.10/1.31  thf('35', plain,
% 1.10/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.10/1.31           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.10/1.31  thf('36', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.10/1.31           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['34', '35'])).
% 1.10/1.31  thf('37', plain,
% 1.10/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.10/1.31           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.10/1.31  thf('38', plain,
% 1.10/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.10/1.31           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.10/1.31  thf('39', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3)
% 1.10/1.31           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X0 @ X3)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['37', '38'])).
% 1.10/1.31  thf('40', plain,
% 1.10/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.10/1.31           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.10/1.31  thf('41', plain,
% 1.10/1.31      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 1.10/1.31           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.10/1.31  thf('42', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X3))
% 1.10/1.31           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X3))))),
% 1.10/1.31      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.10/1.31  thf('43', plain,
% 1.10/1.31      (![X16 : $i, X17 : $i]:
% 1.10/1.31         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 1.10/1.31      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.10/1.31  thf('44', plain,
% 1.10/1.31      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.10/1.31      inference('demod', [status(thm)], ['36', '42', '43'])).
% 1.10/1.31  thf(l32_xboole_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.10/1.31  thf('45', plain,
% 1.10/1.31      (![X3 : $i, X4 : $i]:
% 1.10/1.31         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 1.10/1.31      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.10/1.31  thf('46', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['44', '45'])).
% 1.10/1.31  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.10/1.31      inference('simplify', [status(thm)], ['46'])).
% 1.10/1.31  thf(t3_subset, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.10/1.31  thf('48', plain,
% 1.10/1.31      (![X27 : $i, X29 : $i]:
% 1.10/1.31         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 1.10/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.10/1.31  thf('49', plain,
% 1.10/1.31      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['47', '48'])).
% 1.10/1.31  thf(d5_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.31       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.10/1.31  thf('50', plain,
% 1.10/1.31      (![X18 : $i, X19 : $i]:
% 1.10/1.31         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 1.10/1.31          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 1.10/1.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.10/1.31  thf('51', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['49', '50'])).
% 1.10/1.31  thf(d10_xboole_0, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.10/1.31  thf('52', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.10/1.31      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.10/1.31  thf('53', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.10/1.31      inference('simplify', [status(thm)], ['52'])).
% 1.10/1.31  thf('54', plain,
% 1.10/1.31      (![X27 : $i, X29 : $i]:
% 1.10/1.31         ((m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X27 @ X29))),
% 1.10/1.31      inference('cnf', [status(esa)], [t3_subset])).
% 1.10/1.31  thf('55', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['53', '54'])).
% 1.10/1.31  thf(involutiveness_k3_subset_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.10/1.31       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.10/1.31  thf('56', plain,
% 1.10/1.31      (![X22 : $i, X23 : $i]:
% 1.10/1.31         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 1.10/1.31          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 1.10/1.31      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.10/1.31  thf('57', plain,
% 1.10/1.31      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['55', '56'])).
% 1.10/1.31  thf('58', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['53', '54'])).
% 1.10/1.31  thf('59', plain,
% 1.10/1.31      (![X18 : $i, X19 : $i]:
% 1.10/1.31         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 1.10/1.31          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 1.10/1.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.10/1.31  thf('60', plain,
% 1.10/1.31      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['58', '59'])).
% 1.10/1.31  thf('61', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.10/1.31      inference('simplify', [status(thm)], ['52'])).
% 1.10/1.31  thf('62', plain,
% 1.10/1.31      (![X3 : $i, X5 : $i]:
% 1.10/1.31         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.10/1.31      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.10/1.31  thf('63', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.10/1.31      inference('sup-', [status(thm)], ['61', '62'])).
% 1.10/1.31  thf('64', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.10/1.31      inference('sup+', [status(thm)], ['60', '63'])).
% 1.10/1.31  thf('65', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.10/1.31      inference('demod', [status(thm)], ['57', '64'])).
% 1.10/1.31  thf('66', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.10/1.31      inference('demod', [status(thm)], ['51', '65'])).
% 1.10/1.31  thf('67', plain,
% 1.10/1.31      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.10/1.31      inference('demod', [status(thm)], ['12', '24', '30', '33', '66'])).
% 1.10/1.31  thf('68', plain,
% 1.10/1.31      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.10/1.31         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('69', plain, ($false),
% 1.10/1.31      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.10/1.31  
% 1.10/1.31  % SZS output end Refutation
% 1.10/1.31  
% 1.10/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
