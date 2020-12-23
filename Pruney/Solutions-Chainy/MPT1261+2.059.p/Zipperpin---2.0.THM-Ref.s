%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VQCkBsPCSE

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:46 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 264 expanded)
%              Number of leaves         :   34 (  87 expanded)
%              Depth                    :   17
%              Number of atoms          :  992 (3474 expanded)
%              Number of equality atoms :   77 ( 227 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k6_subset_1 @ X17 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('10',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k2_tops_1 @ sk_A @ sk_B ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_tops_1 @ X32 @ X31 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k2_pre_topc @ X32 @ X31 ) @ ( k1_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('29',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_pre_topc @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
       != X25 )
      | ( v4_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','50'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','64'])).

thf('66',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['29'])).

thf('67',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['47','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('70',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['38','74'])).

thf('76',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['32','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VQCkBsPCSE
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:52:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 399 iterations in 0.238s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.70  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.46/0.70  thf(t77_tops_1, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70           ( ( v4_pre_topc @ B @ A ) <=>
% 0.46/0.70             ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.70               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.70          ( ![B:$i]:
% 0.46/0.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70              ( ( v4_pre_topc @ B @ A ) <=>
% 0.46/0.70                ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.70                  ( k7_subset_1 @
% 0.46/0.70                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70              (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.70        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70             (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.70        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.46/0.70          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.70  thf(redefinition_k6_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.46/0.70          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k6_subset_1 @ X17 @ X19)))),
% 0.46/0.70      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.70           = (k6_subset_1 @ sk_B @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.70        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['2', '7'])).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.70           = (k6_subset_1 @ sk_B @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70              (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.70         <= (~
% 0.46/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.70         <= (~
% 0.46/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.70         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.46/0.70         <= (~
% 0.46/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['8', '11'])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (((v4_pre_topc @ sk_B @ sk_A))
% 0.46/0.70         <= (~
% 0.46/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t52_pre_topc, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_pre_topc @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.46/0.70             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.46/0.70               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.46/0.70          | ~ (v4_pre_topc @ X25 @ X26)
% 0.46/0.70          | ((k2_pre_topc @ X26 @ X25) = (X25))
% 0.46/0.70          | ~ (l1_pre_topc @ X26))),
% 0.46/0.70      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.70        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.46/0.70        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.46/0.70         <= (~
% 0.46/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['13', '18'])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(l78_tops_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_pre_topc @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70           ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.70             ( k7_subset_1 @
% 0.46/0.70               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.46/0.70               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.46/0.70          | ((k2_tops_1 @ X32 @ X31)
% 0.46/0.70              = (k7_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.46/0.70                 (k2_pre_topc @ X32 @ X31) @ (k1_tops_1 @ X32 @ X31)))
% 0.46/0.70          | ~ (l1_pre_topc @ X32))),
% 0.46/0.70      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.70        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.70               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.46/0.70            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70             (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.70         <= (~
% 0.46/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['19', '24'])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.70           = (k6_subset_1 @ sk_B @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.70         <= (~
% 0.46/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          != (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.70         <= (~
% 0.46/0.70             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.46/0.70       ~
% 0.46/0.70       (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('31', plain, (~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain, (~ (v4_pre_topc @ sk_B @ sk_A)),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.46/0.70          | ~ (v2_pre_topc @ X26)
% 0.46/0.70          | ((k2_pre_topc @ X26 @ X25) != (X25))
% 0.46/0.70          | (v4_pre_topc @ X25 @ X26)
% 0.46/0.70          | ~ (l1_pre_topc @ X26))),
% 0.46/0.70      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.70        | (v4_pre_topc @ sk_B @ sk_A)
% 0.46/0.70        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.46/0.70        | ~ (v2_pre_topc @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.70  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(dt_k2_tops_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.70       ( m1_subset_1 @
% 0.46/0.70         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (![X27 : $i, X28 : $i]:
% 0.46/0.70         (~ (l1_pre_topc @ X27)
% 0.46/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.70          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 0.46/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.70  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.70  thf('44', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k4_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.70       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.46/0.70          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.46/0.70          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.70            = (k2_xboole_0 @ sk_B @ X0))
% 0.46/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.70         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['43', '46'])).
% 0.46/0.70  thf('48', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.70           = (k6_subset_1 @ sk_B @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.70  thf('49', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70             (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.70        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70             (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('split', [status(esa)], ['49'])).
% 0.46/0.70  thf('51', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['48', '50'])).
% 0.46/0.70  thf(dt_k6_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      (![X10 : $i, X11 : $i]:
% 0.46/0.70         (m1_subset_1 @ (k6_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.46/0.70  thf(t3_subset, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X22 : $i, X23 : $i]:
% 0.46/0.70         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.70  thf('54', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.46/0.70      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.70  thf(t28_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X4 : $i, X5 : $i]:
% 0.46/0.70         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0)
% 0.46/0.70           = (k6_subset_1 @ X0 @ X1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.70  thf(commutativity_k2_tarski, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.70  thf('57', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.46/0.70      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.70  thf(t12_setfam_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i]:
% 0.46/0.70         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i]:
% 0.46/0.70         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.70      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.70  thf('62', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.46/0.70           = (k6_subset_1 @ X0 @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['56', '61'])).
% 0.46/0.70  thf(t22_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)) = (X1))),
% 0.46/0.70      inference('sup+', [status(thm)], ['62', '63'])).
% 0.46/0.70  thf('65', plain,
% 0.46/0.70      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.46/0.70         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['51', '64'])).
% 0.46/0.70  thf('66', plain,
% 0.46/0.70      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.70          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['29'])).
% 0.46/0.70  thf('67', plain,
% 0.46/0.70      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.46/0.70  thf('68', plain,
% 0.46/0.70      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.70         = (sk_B))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '67'])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t65_tops_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_pre_topc @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70           ( ( k2_pre_topc @ A @ B ) =
% 0.46/0.70             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.70  thf('70', plain,
% 0.46/0.70      (![X33 : $i, X34 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.46/0.70          | ((k2_pre_topc @ X34 @ X33)
% 0.46/0.70              = (k4_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.46/0.70                 (k2_tops_1 @ X34 @ X33)))
% 0.46/0.70          | ~ (l1_pre_topc @ X34))),
% 0.46/0.70      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.70        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.46/0.70            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.70  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      (((k2_pre_topc @ sk_A @ sk_B)
% 0.46/0.70         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.70            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.70  thf('74', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.46/0.70      inference('sup+', [status(thm)], ['68', '73'])).
% 0.46/0.70  thf('75', plain, (((v4_pre_topc @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.46/0.70      inference('demod', [status(thm)], ['38', '74'])).
% 0.46/0.70  thf('76', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.46/0.70      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.70  thf('77', plain, ($false), inference('demod', [status(thm)], ['32', '76'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
