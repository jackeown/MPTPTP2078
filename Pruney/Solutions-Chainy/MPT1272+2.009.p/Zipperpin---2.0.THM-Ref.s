%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EDmRHzgrsk

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:29 EST 2020

% Result     : Theorem 51.72s
% Output     : Refutation 51.72s
% Verified   : 
% Statistics : Number of formulae       :  530 (49517 expanded)
%              Number of leaves         :   39 (15464 expanded)
%              Depth                    :   36
%              Number of atoms          : 4981 (429305 expanded)
%              Number of equality atoms :  230 (15603 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t91_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tops_1 @ B @ A )
             => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('5',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X44 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X29: $i] :
      ( ( l1_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r1_tarski @ X30 @ ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X29: $i] :
      ( ( l1_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','47'])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X29: $i] :
      ( ( l1_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('56',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('68',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','79'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('81',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('82',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('89',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X18 @ X17 ) @ ( k3_subset_1 @ X18 @ X19 ) )
      | ( r1_tarski @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_subset_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_subset_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','95'])).

thf('97',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('103',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('105',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('106',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('108',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['103','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('111',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X21 @ X20 ) @ X22 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X21 @ X22 ) @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('114',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('119',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('126',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['124','127','128'])).

thf('130',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['108','129'])).

thf('131',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['103','106','107'])).

thf('132',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['103','106','107'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('134',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('136',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('137',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('139',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('142',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('144',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('145',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('147',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('149',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['142','149'])).

thf('151',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('152',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('153',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['139','150','153'])).

thf('155',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('156',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('158',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('165',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['163','168'])).

thf('170',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('171',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('175',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ( r1_tarski @ ( k3_subset_1 @ X18 @ X17 ) @ ( k3_subset_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) @ ( k3_subset_1 @ X0 @ X3 ) )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('178',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) @ ( k3_subset_1 @ X0 @ X3 ) )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) @ ( k3_subset_1 @ X0 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['173','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('183',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('184',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['181','182','188'])).

thf('190',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','189'])).

thf('191',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('192',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('195',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['112','115'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('199',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['197','200','201'])).

thf('203',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['190','202'])).

thf('204',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('205',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B )
    | ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('207',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('208',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('210',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['205','210'])).

thf('212',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['136','211'])).

thf('213',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('214',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['135','214'])).

thf('216',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('217',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['103','106','107'])).

thf('219',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['134','217','218'])).

thf('220',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('222',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('225',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['223','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['222','232'])).

thf('234',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('235',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('237',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('238',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('240',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('241',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('242',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('243',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('245',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('249',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('251',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('252',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['250','251'])).

thf('253',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('254',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('256',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X44 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ X0 @ X1 ) @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['254','258'])).

thf('260',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('262',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v2_tops_1 @ X45 @ X46 )
      | ( ( k1_tops_1 @ X46 @ X45 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('263',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('266',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v3_tops_1 @ X41 @ X42 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X42 @ X41 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('267',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['267','268','269'])).

thf('271',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['263','264','270'])).

thf('272',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['259','260','271'])).

thf('273',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    r1_tarski @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['249','274'])).

thf('276',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('277',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['242','277'])).

thf('279',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('280',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('281',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('282',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['278','279'])).

thf('284',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('285',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('287',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['282','285','286'])).

thf('288',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['124','127','128'])).

thf('289',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['124','127','128'])).

thf('290',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['124','127','128'])).

thf('292',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('293',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('294',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['290','291','292','293'])).

thf('295',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['287','294'])).

thf('296',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','219'])).

thf('297',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['282','285','286'])).

thf('298',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('299',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('300',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 ) ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('304',plain,(
    ! [X0: $i] :
      ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['301','302','303'])).

thf('305',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('306',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['304','305','306'])).

thf('308',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['298','307'])).

thf('309',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('310',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','219'])).

thf('311',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('313',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('314',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('315',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 ) @ X40 )
      | ( v2_tops_1 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('316',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('318',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['316','317'])).

thf('319',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( v2_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['313','318'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('321',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('322',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k2_pre_topc @ X38 @ X37 )
       != ( k2_struct_0 @ X38 ) )
      | ( v1_tops_1 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('323',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['321','322'])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['320','323'])).

thf('325',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['324'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('327',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(clc,[status(thm)],['325','326'])).

thf('328',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['319','327'])).

thf('329',plain,(
    ! [X0: $i] :
      ( ( v2_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['312','328'])).

thf('330',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['329'])).

thf('331',plain,(
    ! [X0: $i] :
      ( ( v2_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['311','330'])).

thf('332',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['331'])).

thf('333',plain,
    ( ( v2_tops_1 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['310','332'])).

thf('334',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v2_tops_1 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['333','334'])).

thf('336',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('337',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v2_tops_1 @ X45 @ X46 )
      | ( ( k1_tops_1 @ X46 @ X45 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('338',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v2_tops_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['336','337'])).

thf('339',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v2_tops_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['338','339'])).

thf('341',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['335','340'])).

thf('342',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('343',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['341','342'])).

thf('344',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('345',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('346',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['344','345'])).

thf('347',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('348',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('349',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['347','348'])).

thf('350',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('351',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('352',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['349','350','351'])).

thf('353',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('354',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['308','309','343','346','352','353'])).

thf('355',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','237','238','239','240','241','354'])).

thf('356',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('357',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('358',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('360',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['358','359'])).

thf('361',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('362',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('363',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['361','362'])).

thf('364',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('365',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['360','363','364'])).

thf('366',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('367',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['365','366'])).

thf('368',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('369',plain,(
    r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['367','368'])).

thf('370',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['308','309','343','346','352','353'])).

thf('371',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('372',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['290','291','292','293'])).

thf('373',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['371','372'])).

thf('374',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','219'])).

thf('375',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('376',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['373','374','375'])).

thf('377',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['295','296','297'])).

thf('378',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['376','377'])).

thf('379',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['370','378'])).

thf('380',plain,(
    r1_tarski @ k1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['369','379'])).

thf('381',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('382',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['380','381'])).

thf('383',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k1_tops_1 @ X46 @ X45 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X45 @ X46 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('385',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['383','384'])).

thf('386',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['385','386'])).

thf('388',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('389',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v2_tops_1 @ X39 @ X40 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 ) @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('390',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['388','389'])).

thf('391',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('392',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['142','149'])).

thf('393',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['390','391','392'])).

thf('394',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('395',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('396',plain,
    ( ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['394','395'])).

thf('397',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('398',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['396','397'])).

thf('399',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('400',plain,(
    ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['398','399'])).

thf('401',plain,(
    ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['393','400'])).

thf('402',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['387','401'])).

thf('403',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['382','402'])).

thf('404',plain,(
    ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['355','403'])).

thf('405',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('406',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('407',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['405','406'])).

thf('408',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X44 @ X43 ) @ X43 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('409',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['409'])).

thf('411',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('412',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('413',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['411','412'])).

thf('414',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('415',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('416',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['414','415'])).

thf('417',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('418',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('419',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('420',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['418','419'])).

thf('421',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 ) ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('422',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['420','421'])).

thf('423',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('424',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('425',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('426',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['424','425'])).

thf('427',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['142','149'])).

thf('428',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['426','427'])).

thf('429',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['422','423','428'])).

thf('430',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['417','429'])).

thf('431',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['414','415'])).

thf('432',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('433',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['430','431','432'])).

thf('434',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['416','433'])).

thf('435',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['413','434'])).

thf('436',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('437',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( r1_tarski @ X32 @ X34 )
      | ( r1_tarski @ ( k2_pre_topc @ X33 @ X32 ) @ ( k2_pre_topc @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('438',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ X1 ) @ ( k2_pre_topc @ X0 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['436','437'])).

thf('439',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['435','438'])).

thf('440',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('441',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('442',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('443',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['439','440','441','442'])).

thf('444',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['413','434'])).

thf('445',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('446',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v1_tops_1 @ X37 @ X38 )
      | ( ( k2_pre_topc @ X38 @ X37 )
        = ( k2_struct_0 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('447',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['445','446'])).

thf('448',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_tops_1 @ X1 @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['447'])).

thf('449',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['444','448'])).

thf('450',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('451',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('452',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('453',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v2_tops_1 @ X39 @ X40 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 ) @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('454',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v2_tops_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['452','453'])).

thf('455',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tops_1 @ X1 @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['454'])).

thf('456',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['451','455'])).

thf('457',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('458',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['422','423','428'])).

thf('459',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['267','268','269'])).

thf('460',plain,(
    v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['456','457','458','459'])).

thf('461',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['449','450','460'])).

thf('462',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['443','461'])).

thf('463',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['410','462'])).

thf('464',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('465',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('466',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('467',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('468',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('469',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['467','468'])).

thf('470',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['466','469'])).

thf('471',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('472',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['470','471'])).

thf('473',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('474',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['472','473'])).

thf('475',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('476',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['474','475'])).

thf('477',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('478',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ ( k2_pre_topc @ X36 @ ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 ) ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('479',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['477','478'])).

thf('480',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('481',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['142','149'])).

thf('482',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['479','480','481'])).

thf('483',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['233','234','235','236'])).

thf('484',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['482','483'])).

thf('485',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['476','484'])).

thf('486',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('487',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['485','486'])).

thf('488',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['463','464','465','487'])).

thf('489',plain,(
    $false ),
    inference(demod,[status(thm)],['404','488'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EDmRHzgrsk
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:07:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 51.72/51.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 51.72/51.93  % Solved by: fo/fo7.sh
% 51.72/51.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.72/51.93  % done 74435 iterations in 51.466s
% 51.72/51.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 51.72/51.93  % SZS output start Refutation
% 51.72/51.93  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 51.72/51.93  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 51.72/51.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 51.72/51.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 51.72/51.93  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 51.72/51.93  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 51.72/51.93  thf(sk_A_type, type, sk_A: $i).
% 51.72/51.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 51.72/51.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.72/51.93  thf(sk_B_type, type, sk_B: $i).
% 51.72/51.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.72/51.93  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 51.72/51.93  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 51.72/51.93  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 51.72/51.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 51.72/51.93  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 51.72/51.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 51.72/51.93  thf(d3_struct_0, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 51.72/51.93  thf('0', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf(t91_tops_1, conjecture,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( ( v3_tops_1 @ B @ A ) =>
% 51.72/51.93             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 51.72/51.93  thf(zf_stmt_0, negated_conjecture,
% 51.72/51.93    (~( ![A:$i]:
% 51.72/51.93        ( ( l1_pre_topc @ A ) =>
% 51.72/51.93          ( ![B:$i]:
% 51.72/51.93            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93              ( ( v3_tops_1 @ B @ A ) =>
% 51.72/51.93                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 51.72/51.93    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 51.72/51.93  thf('1', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf(t3_subset, axiom,
% 51.72/51.93    (![A:$i,B:$i]:
% 51.72/51.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 51.72/51.93  thf('2', plain,
% 51.72/51.93      (![X23 : $i, X24 : $i]:
% 51.72/51.93         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['1', '2'])).
% 51.72/51.93  thf('4', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf(t44_tops_1, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 51.72/51.93  thf('5', plain,
% 51.72/51.93      (![X43 : $i, X44 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 51.72/51.93          | (r1_tarski @ (k1_tops_1 @ X44 @ X43) @ X43)
% 51.72/51.93          | ~ (l1_pre_topc @ X44))),
% 51.72/51.93      inference('cnf', [status(esa)], [t44_tops_1])).
% 51.72/51.93  thf('6', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['4', '5'])).
% 51.72/51.93  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('8', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 51.72/51.93      inference('demod', [status(thm)], ['6', '7'])).
% 51.72/51.93  thf(t1_xboole_1, axiom,
% 51.72/51.93    (![A:$i,B:$i,C:$i]:
% 51.72/51.93     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 51.72/51.93       ( r1_tarski @ A @ C ) ))).
% 51.72/51.93  thf('9', plain,
% 51.72/51.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 51.72/51.93         (~ (r1_tarski @ X6 @ X7)
% 51.72/51.93          | ~ (r1_tarski @ X7 @ X8)
% 51.72/51.93          | (r1_tarski @ X6 @ X8))),
% 51.72/51.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 51.72/51.93  thf('10', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 51.72/51.93          | ~ (r1_tarski @ sk_B @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['8', '9'])).
% 51.72/51.93  thf('11', plain,
% 51.72/51.93      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['3', '10'])).
% 51.72/51.93  thf('12', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('13', plain,
% 51.72/51.93      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['11', '12'])).
% 51.72/51.93  thf('14', plain,
% 51.72/51.93      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 51.72/51.93         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['0', '13'])).
% 51.72/51.93  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf(dt_l1_pre_topc, axiom,
% 51.72/51.93    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 51.72/51.93  thf('16', plain,
% 51.72/51.93      (![X29 : $i]: ((l1_struct_0 @ X29) | ~ (l1_pre_topc @ X29))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 51.72/51.93  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('18', plain,
% 51.72/51.93      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['14', '17'])).
% 51.72/51.93  thf(d5_subset_1, axiom,
% 51.72/51.93    (![A:$i,B:$i]:
% 51.72/51.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.72/51.93       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 51.72/51.93  thf('19', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('20', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['18', '19'])).
% 51.72/51.93  thf('21', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf(d10_xboole_0, axiom,
% 51.72/51.93    (![A:$i,B:$i]:
% 51.72/51.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 51.72/51.93  thf('22', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.72/51.93  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 51.72/51.93      inference('simplify', [status(thm)], ['22'])).
% 51.72/51.93  thf('24', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('25', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['23', '24'])).
% 51.72/51.93  thf(t48_pre_topc, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 51.72/51.93  thf('26', plain,
% 51.72/51.93      (![X30 : $i, X31 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 51.72/51.93          | (r1_tarski @ X30 @ (k2_pre_topc @ X31 @ X30))
% 51.72/51.93          | ~ (l1_pre_topc @ X31))),
% 51.72/51.93      inference('cnf', [status(esa)], [t48_pre_topc])).
% 51.72/51.93  thf('27', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 51.72/51.93             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['25', '26'])).
% 51.72/51.93  thf('28', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['23', '24'])).
% 51.72/51.93  thf(dt_k2_pre_topc, axiom,
% 51.72/51.93    (![A:$i,B:$i]:
% 51.72/51.93     ( ( ( l1_pre_topc @ A ) & 
% 51.72/51.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 51.72/51.93       ( m1_subset_1 @
% 51.72/51.93         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 51.72/51.93  thf('29', plain,
% 51.72/51.93      (![X27 : $i, X28 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X27)
% 51.72/51.93          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 51.72/51.93          | (m1_subset_1 @ (k2_pre_topc @ X27 @ X28) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 51.72/51.93  thf('30', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 51.72/51.93           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['28', '29'])).
% 51.72/51.93  thf('31', plain,
% 51.72/51.93      (![X23 : $i, X24 : $i]:
% 51.72/51.93         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('32', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 51.72/51.93             (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['30', '31'])).
% 51.72/51.93  thf('33', plain,
% 51.72/51.93      (![X0 : $i, X2 : $i]:
% 51.72/51.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 51.72/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.72/51.93  thf('34', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 51.72/51.93               (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['32', '33'])).
% 51.72/51.93  thf('35', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['27', '34'])).
% 51.72/51.93  thf('36', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('simplify', [status(thm)], ['35'])).
% 51.72/51.93  thf('37', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('38', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 51.72/51.93           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['28', '29'])).
% 51.72/51.93  thf('39', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 51.72/51.93           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_struct_0 @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup+', [status(thm)], ['37', '38'])).
% 51.72/51.93  thf('40', plain,
% 51.72/51.93      (![X29 : $i]: ((l1_struct_0 @ X29) | ~ (l1_pre_topc @ X29))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 51.72/51.93  thf('41', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 51.72/51.93      inference('clc', [status(thm)], ['39', '40'])).
% 51.72/51.93  thf('42', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup+', [status(thm)], ['36', '41'])).
% 51.72/51.93  thf('43', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['42'])).
% 51.72/51.93  thf('44', plain,
% 51.72/51.93      (![X23 : $i, X24 : $i]:
% 51.72/51.93         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('45', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['43', '44'])).
% 51.72/51.93  thf('46', plain,
% 51.72/51.93      (![X0 : $i, X2 : $i]:
% 51.72/51.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 51.72/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.72/51.93  thf('47', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 51.72/51.93          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['45', '46'])).
% 51.72/51.93  thf('48', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 51.72/51.93          | ~ (l1_struct_0 @ X0)
% 51.72/51.93          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['21', '47'])).
% 51.72/51.93  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 51.72/51.93      inference('simplify', [status(thm)], ['22'])).
% 51.72/51.93  thf('50', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_struct_0 @ X0)
% 51.72/51.93          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('demod', [status(thm)], ['48', '49'])).
% 51.72/51.93  thf('51', plain,
% 51.72/51.93      (![X29 : $i]: ((l1_struct_0 @ X29) | ~ (l1_pre_topc @ X29))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 51.72/51.93  thf('52', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('53', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('simplify', [status(thm)], ['35'])).
% 51.72/51.93  thf('54', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('55', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 51.72/51.93             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['25', '26'])).
% 51.72/51.93  thf('56', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('57', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['55', '56'])).
% 51.72/51.93  thf('58', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 51.72/51.93           (k1_zfmisc_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup+', [status(thm)], ['54', '57'])).
% 51.72/51.93  thf('59', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['58'])).
% 51.72/51.93  thf('60', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 51.72/51.93           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup+', [status(thm)], ['53', '59'])).
% 51.72/51.93  thf('61', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['60'])).
% 51.72/51.93  thf('62', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('63', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 51.72/51.93              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['61', '62'])).
% 51.72/51.93  thf('64', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['60'])).
% 51.72/51.93  thf(involutiveness_k3_subset_1, axiom,
% 51.72/51.93    (![A:$i,B:$i]:
% 51.72/51.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.72/51.93       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 51.72/51.93  thf('65', plain,
% 51.72/51.93      (![X15 : $i, X16 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 51.72/51.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 51.72/51.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.72/51.93  thf('66', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93              (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))
% 51.72/51.93              = (k2_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['64', '65'])).
% 51.72/51.93  thf('67', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['60'])).
% 51.72/51.93  thf(dt_k3_subset_1, axiom,
% 51.72/51.93    (![A:$i,B:$i]:
% 51.72/51.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.72/51.93       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 51.72/51.93  thf('68', plain,
% 51.72/51.93      (![X13 : $i, X14 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 51.72/51.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 51.72/51.93  thf('69', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ 
% 51.72/51.93             (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['67', '68'])).
% 51.72/51.93  thf('70', plain,
% 51.72/51.93      (![X13 : $i, X14 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 51.72/51.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 51.72/51.93  thf('71', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ 
% 51.72/51.93             (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93              (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['69', '70'])).
% 51.72/51.93  thf('72', plain,
% 51.72/51.93      (![X23 : $i, X24 : $i]:
% 51.72/51.93         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('73', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ 
% 51.72/51.93             (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93              (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))) @ 
% 51.72/51.93             (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['71', '72'])).
% 51.72/51.93  thf('74', plain,
% 51.72/51.93      (![X0 : $i, X2 : $i]:
% 51.72/51.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 51.72/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.72/51.93  thf('75', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 51.72/51.93               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93                (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))))
% 51.72/51.93          | ((u1_struct_0 @ X0)
% 51.72/51.93              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93                 (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['73', '74'])).
% 51.72/51.93  thf('76', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((u1_struct_0 @ X0)
% 51.72/51.93              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93                 (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['66', '75'])).
% 51.72/51.93  thf('77', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0)
% 51.72/51.93            = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93               (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 51.72/51.93      inference('simplify', [status(thm)], ['76'])).
% 51.72/51.93  thf('78', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['43', '44'])).
% 51.72/51.93  thf('79', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((u1_struct_0 @ X0)
% 51.72/51.93              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93                 (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))))),
% 51.72/51.93      inference('clc', [status(thm)], ['77', '78'])).
% 51.72/51.93  thf('80', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0)
% 51.72/51.93            = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93               (k4_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup+', [status(thm)], ['63', '79'])).
% 51.72/51.93  thf(t36_xboole_1, axiom,
% 51.72/51.93    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 51.72/51.93  thf('81', plain,
% 51.72/51.93      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 51.72/51.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.72/51.93  thf('82', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('83', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['81', '82'])).
% 51.72/51.93  thf('84', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('85', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf('86', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0)
% 51.72/51.93            = (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93               (k4_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('demod', [status(thm)], ['80', '85'])).
% 51.72/51.93  thf('87', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((u1_struct_0 @ X0)
% 51.72/51.93              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93                 (k4_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['86'])).
% 51.72/51.93  thf('88', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf(t31_subset_1, axiom,
% 51.72/51.93    (![A:$i,B:$i]:
% 51.72/51.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.72/51.93       ( ![C:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 51.72/51.93           ( ( r1_tarski @ B @ C ) <=>
% 51.72/51.93             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 51.72/51.93  thf('89', plain,
% 51.72/51.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 51.72/51.93          | ~ (r1_tarski @ (k3_subset_1 @ X18 @ X17) @ 
% 51.72/51.93               (k3_subset_1 @ X18 @ X19))
% 51.72/51.93          | (r1_tarski @ X19 @ X17)
% 51.72/51.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t31_subset_1])).
% 51.72/51.93  thf('90', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 51.72/51.93             (k3_subset_1 @ X1 @ X2))
% 51.72/51.93          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 51.72/51.93          | (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 51.72/51.93          | ~ (m1_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['88', '89'])).
% 51.72/51.93  thf('91', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['81', '82'])).
% 51.72/51.93  thf('92', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 51.72/51.93             (k3_subset_1 @ X1 @ X2))
% 51.72/51.93          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 51.72/51.93          | (r1_tarski @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.72/51.93      inference('demod', [status(thm)], ['90', '91'])).
% 51.72/51.93  thf('93', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 51.72/51.93             (k3_subset_1 @ (u1_struct_0 @ X0) @ X1))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ X1 @ 
% 51.72/51.93             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['87', '92'])).
% 51.72/51.93  thf('94', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 51.72/51.93             (k3_subset_1 @ (k2_struct_0 @ X0) @ X1))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | (r1_tarski @ X1 @ 
% 51.72/51.93             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['52', '93'])).
% 51.72/51.93  thf('95', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((r1_tarski @ X1 @ 
% 51.72/51.93           (k4_xboole_0 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 51.72/51.93               (k3_subset_1 @ (k2_struct_0 @ X0) @ X1)))),
% 51.72/51.93      inference('simplify', [status(thm)], ['94'])).
% 51.72/51.93  thf('96', plain,
% 51.72/51.93      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93           (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 51.72/51.93        | ~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.72/51.93        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 51.72/51.93           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['20', '95'])).
% 51.72/51.93  thf('97', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('98', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('99', plain,
% 51.72/51.93      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['97', '98'])).
% 51.72/51.93  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('101', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['99', '100'])).
% 51.72/51.93  thf('102', plain,
% 51.72/51.93      (![X15 : $i, X16 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 51.72/51.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 51.72/51.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.72/51.93  thf('103', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['101', '102'])).
% 51.72/51.93  thf('104', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['99', '100'])).
% 51.72/51.93  thf('105', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('106', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['104', '105'])).
% 51.72/51.93  thf('107', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf('108', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['103', '106', '107'])).
% 51.72/51.93  thf('109', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['81', '82'])).
% 51.72/51.93  thf('110', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['23', '24'])).
% 51.72/51.93  thf(t36_subset_1, axiom,
% 51.72/51.93    (![A:$i,B:$i]:
% 51.72/51.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 51.72/51.93       ( ![C:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 51.72/51.93           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 51.72/51.93             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 51.72/51.93  thf('111', plain,
% 51.72/51.93      (![X20 : $i, X21 : $i, X22 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 51.72/51.93          | (r1_tarski @ (k3_subset_1 @ X21 @ X20) @ X22)
% 51.72/51.93          | ~ (r1_tarski @ (k3_subset_1 @ X21 @ X22) @ X20)
% 51.72/51.93          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t36_subset_1])).
% 51.72/51.93  thf('112', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 51.72/51.93          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 51.72/51.93          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 51.72/51.93      inference('sup-', [status(thm)], ['110', '111'])).
% 51.72/51.93  thf('113', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['23', '24'])).
% 51.72/51.93  thf('114', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('115', plain,
% 51.72/51.93      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['113', '114'])).
% 51.72/51.93  thf('116', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 51.72/51.93          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 51.72/51.93          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['112', '115'])).
% 51.72/51.93  thf('117', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)) @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['109', '116'])).
% 51.72/51.93  thf('118', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf('119', plain,
% 51.72/51.93      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 51.72/51.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.72/51.93  thf('120', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['117', '118', '119'])).
% 51.72/51.93  thf('121', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('122', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X1 @ X1) @ 
% 51.72/51.93          (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['120', '121'])).
% 51.72/51.93  thf('123', plain,
% 51.72/51.93      (![X15 : $i, X16 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 51.72/51.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 51.72/51.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.72/51.93  thf('124', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.72/51.93           (k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1)))
% 51.72/51.93           = (k4_xboole_0 @ X1 @ X1))),
% 51.72/51.93      inference('sup-', [status(thm)], ['122', '123'])).
% 51.72/51.93  thf('125', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X1 @ X1) @ 
% 51.72/51.93          (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['120', '121'])).
% 51.72/51.93  thf('126', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('127', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['125', '126'])).
% 51.72/51.93  thf('128', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf('129', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.72/51.93           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1)))
% 51.72/51.93           = (k4_xboole_0 @ X1 @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['124', '127', '128'])).
% 51.72/51.93  thf('130', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ 
% 51.72/51.93         (k4_xboole_0 @ 
% 51.72/51.93          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93           (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup+', [status(thm)], ['108', '129'])).
% 51.72/51.93  thf('131', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['103', '106', '107'])).
% 51.72/51.93  thf('132', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['103', '106', '107'])).
% 51.72/51.93  thf('133', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['125', '126'])).
% 51.72/51.93  thf('134', plain,
% 51.72/51.93      (((k3_subset_1 @ sk_B @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 51.72/51.93         = (k4_xboole_0 @ 
% 51.72/51.93            (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93             (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93            (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))),
% 51.72/51.93      inference('sup+', [status(thm)], ['132', '133'])).
% 51.72/51.93  thf('135', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('136', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('137', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('138', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 51.72/51.93          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 51.72/51.93          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['112', '115'])).
% 51.72/51.93  thf('139', plain,
% 51.72/51.93      (((r1_tarski @ 
% 51.72/51.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)
% 51.72/51.93        | ~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 51.72/51.93             (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['137', '138'])).
% 51.72/51.93  thf('140', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('141', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('142', plain,
% 51.72/51.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['140', '141'])).
% 51.72/51.93  thf('143', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('144', plain,
% 51.72/51.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['140', '141'])).
% 51.72/51.93  thf('145', plain,
% 51.72/51.93      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['143', '144'])).
% 51.72/51.93  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('147', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['145', '146'])).
% 51.72/51.93  thf('148', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['104', '105'])).
% 51.72/51.93  thf('149', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['147', '148'])).
% 51.72/51.93  thf('150', plain,
% 51.72/51.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['142', '149'])).
% 51.72/51.93  thf('151', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['147', '148'])).
% 51.72/51.93  thf('152', plain,
% 51.72/51.93      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 51.72/51.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.72/51.93  thf('153', plain,
% 51.72/51.93      ((r1_tarski @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 51.72/51.93        (u1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['151', '152'])).
% 51.72/51.93  thf('154', plain,
% 51.72/51.93      ((r1_tarski @ 
% 51.72/51.93        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)),
% 51.72/51.93      inference('demod', [status(thm)], ['139', '150', '153'])).
% 51.72/51.93  thf('155', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('156', plain,
% 51.72/51.93      ((m1_subset_1 @ 
% 51.72/51.93        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 51.72/51.93        (k1_zfmisc_1 @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['154', '155'])).
% 51.72/51.93  thf('157', plain,
% 51.72/51.93      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 51.72/51.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.72/51.93  thf(t109_xboole_1, axiom,
% 51.72/51.93    (![A:$i,B:$i,C:$i]:
% 51.72/51.93     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 51.72/51.93  thf('158', plain,
% 51.72/51.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 51.72/51.93         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k4_xboole_0 @ X3 @ X5) @ X4))),
% 51.72/51.93      inference('cnf', [status(esa)], [t109_xboole_1])).
% 51.72/51.93  thf('159', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 51.72/51.93      inference('sup-', [status(thm)], ['157', '158'])).
% 51.72/51.93  thf('160', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('161', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 51.72/51.93          (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['159', '160'])).
% 51.72/51.93  thf('162', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 51.72/51.93          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 51.72/51.93          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['112', '115'])).
% 51.72/51.93  thf('163', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ 
% 51.72/51.93           (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))
% 51.72/51.93          | ~ (r1_tarski @ 
% 51.72/51.93               (k3_subset_1 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)) @ 
% 51.72/51.93               X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['161', '162'])).
% 51.72/51.93  thf('164', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 51.72/51.93          (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['159', '160'])).
% 51.72/51.93  thf('165', plain,
% 51.72/51.93      (![X13 : $i, X14 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 51.72/51.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 51.72/51.93  thf('166', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (m1_subset_1 @ 
% 51.72/51.93          (k3_subset_1 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)) @ 
% 51.72/51.93          (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['164', '165'])).
% 51.72/51.93  thf('167', plain,
% 51.72/51.93      (![X23 : $i, X24 : $i]:
% 51.72/51.93         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('168', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (r1_tarski @ 
% 51.72/51.93          (k3_subset_1 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)) @ 
% 51.72/51.93          X0)),
% 51.72/51.93      inference('sup-', [status(thm)], ['166', '167'])).
% 51.72/51.93  thf('169', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ 
% 51.72/51.93          (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['163', '168'])).
% 51.72/51.93  thf('170', plain,
% 51.72/51.93      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 51.72/51.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.72/51.93  thf('171', plain,
% 51.72/51.93      (![X0 : $i, X2 : $i]:
% 51.72/51.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 51.72/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.72/51.93  thf('172', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['170', '171'])).
% 51.72/51.93  thf('173', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ X1 @ X1)
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['169', '172'])).
% 51.72/51.93  thf('174', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 51.72/51.93          (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['159', '160'])).
% 51.72/51.93  thf('175', plain,
% 51.72/51.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 51.72/51.93          | ~ (r1_tarski @ X19 @ X17)
% 51.72/51.93          | (r1_tarski @ (k3_subset_1 @ X18 @ X17) @ (k3_subset_1 @ X18 @ X19))
% 51.72/51.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t31_subset_1])).
% 51.72/51.93  thf('176', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X0))
% 51.72/51.93          | (r1_tarski @ 
% 51.72/51.93             (k3_subset_1 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)) @ 
% 51.72/51.93             (k3_subset_1 @ X0 @ X3))
% 51.72/51.93          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['174', '175'])).
% 51.72/51.93  thf('177', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 51.72/51.93          (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['159', '160'])).
% 51.72/51.93  thf('178', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('179', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['177', '178'])).
% 51.72/51.93  thf('180', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X0))
% 51.72/51.93          | (r1_tarski @ 
% 51.72/51.93             (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)) @ 
% 51.72/51.93             (k3_subset_1 @ X0 @ X3))
% 51.72/51.93          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 51.72/51.93      inference('demod', [status(thm)], ['176', '179'])).
% 51.72/51.93  thf('181', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 51.72/51.93          | (r1_tarski @ 
% 51.72/51.93             (k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)) @ 
% 51.72/51.93             (k3_subset_1 @ X0 @ X2))
% 51.72/51.93          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['173', '180'])).
% 51.72/51.93  thf('182', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ X1 @ X1)
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['169', '172'])).
% 51.72/51.93  thf('183', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['23', '24'])).
% 51.72/51.93  thf('184', plain,
% 51.72/51.93      (![X15 : $i, X16 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 51.72/51.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 51.72/51.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.72/51.93  thf('185', plain,
% 51.72/51.93      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['183', '184'])).
% 51.72/51.93  thf('186', plain,
% 51.72/51.93      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['113', '114'])).
% 51.72/51.93  thf('187', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf('188', plain,
% 51.72/51.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 51.72/51.93      inference('demod', [status(thm)], ['185', '186', '187'])).
% 51.72/51.93  thf('189', plain,
% 51.72/51.93      (![X0 : $i, X2 : $i]:
% 51.72/51.93         (~ (r1_tarski @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 51.72/51.93          | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X2))
% 51.72/51.93          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 51.72/51.93      inference('demod', [status(thm)], ['181', '182', '188'])).
% 51.72/51.93  thf('190', plain,
% 51.72/51.93      (((r1_tarski @ sk_B @ 
% 51.72/51.93         (k3_subset_1 @ sk_B @ 
% 51.72/51.93          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 51.72/51.93        | ~ (r1_tarski @ 
% 51.72/51.93             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 51.72/51.93             (k4_xboole_0 @ sk_B @ sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['156', '189'])).
% 51.72/51.93  thf('191', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['1', '2'])).
% 51.72/51.93  thf('192', plain,
% 51.72/51.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 51.72/51.93         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k4_xboole_0 @ X3 @ X5) @ X4))),
% 51.72/51.93      inference('cnf', [status(esa)], [t109_xboole_1])).
% 51.72/51.93  thf('193', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['191', '192'])).
% 51.72/51.93  thf('194', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('195', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 51.72/51.93          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['193', '194'])).
% 51.72/51.93  thf('196', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 51.72/51.93          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 51.72/51.93          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['112', '115'])).
% 51.72/51.93  thf('197', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((r1_tarski @ 
% 51.72/51.93           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 51.72/51.93           (k4_xboole_0 @ sk_B @ X0))
% 51.72/51.93          | ~ (r1_tarski @ 
% 51.72/51.93               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 51.72/51.93               (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['195', '196'])).
% 51.72/51.93  thf('198', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 51.72/51.93          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['193', '194'])).
% 51.72/51.93  thf('199', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('200', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 51.72/51.93           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['198', '199'])).
% 51.72/51.93  thf('201', plain,
% 51.72/51.93      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 51.72/51.93      inference('cnf', [status(esa)], [t36_xboole_1])).
% 51.72/51.93  thf('202', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (r1_tarski @ 
% 51.72/51.93          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 51.72/51.93          (k4_xboole_0 @ sk_B @ X0))),
% 51.72/51.93      inference('demod', [status(thm)], ['197', '200', '201'])).
% 51.72/51.93  thf('203', plain,
% 51.72/51.93      ((r1_tarski @ sk_B @ 
% 51.72/51.93        (k3_subset_1 @ sk_B @ 
% 51.72/51.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 51.72/51.93      inference('demod', [status(thm)], ['190', '202'])).
% 51.72/51.93  thf('204', plain,
% 51.72/51.93      (![X0 : $i, X2 : $i]:
% 51.72/51.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 51.72/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.72/51.93  thf('205', plain,
% 51.72/51.93      ((~ (r1_tarski @ 
% 51.72/51.93           (k3_subset_1 @ sk_B @ 
% 51.72/51.93            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 51.72/51.93           sk_B)
% 51.72/51.93        | ((k3_subset_1 @ sk_B @ 
% 51.72/51.93            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 51.72/51.93            = (sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['203', '204'])).
% 51.72/51.93  thf('206', plain,
% 51.72/51.93      ((m1_subset_1 @ 
% 51.72/51.93        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 51.72/51.93        (k1_zfmisc_1 @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['154', '155'])).
% 51.72/51.93  thf('207', plain,
% 51.72/51.93      (![X13 : $i, X14 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 51.72/51.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 51.72/51.93  thf('208', plain,
% 51.72/51.93      ((m1_subset_1 @ 
% 51.72/51.93        (k3_subset_1 @ sk_B @ 
% 51.72/51.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 51.72/51.93        (k1_zfmisc_1 @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['206', '207'])).
% 51.72/51.93  thf('209', plain,
% 51.72/51.93      (![X23 : $i, X24 : $i]:
% 51.72/51.93         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('210', plain,
% 51.72/51.93      ((r1_tarski @ 
% 51.72/51.93        (k3_subset_1 @ sk_B @ 
% 51.72/51.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 51.72/51.93        sk_B)),
% 51.72/51.93      inference('sup-', [status(thm)], ['208', '209'])).
% 51.72/51.93  thf('211', plain,
% 51.72/51.93      (((k3_subset_1 @ sk_B @ 
% 51.72/51.93         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) = (
% 51.72/51.93         sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['205', '210'])).
% 51.72/51.93  thf('212', plain,
% 51.72/51.93      ((((k3_subset_1 @ sk_B @ 
% 51.72/51.93          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) = (
% 51.72/51.93          sk_B))
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['136', '211'])).
% 51.72/51.93  thf('213', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('214', plain,
% 51.72/51.93      (((k3_subset_1 @ sk_B @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) = (
% 51.72/51.93         sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['212', '213'])).
% 51.72/51.93  thf('215', plain,
% 51.72/51.93      ((((k3_subset_1 @ sk_B @ 
% 51.72/51.93          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))) = (
% 51.72/51.93          sk_B))
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['135', '214'])).
% 51.72/51.93  thf('216', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('217', plain,
% 51.72/51.93      (((k3_subset_1 @ sk_B @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))) = (
% 51.72/51.93         sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['215', '216'])).
% 51.72/51.93  thf('218', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['103', '106', '107'])).
% 51.72/51.93  thf('219', plain,
% 51.72/51.93      (((sk_B)
% 51.72/51.93         = (k4_xboole_0 @ sk_B @ 
% 51.72/51.93            (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))),
% 51.72/51.93      inference('demod', [status(thm)], ['134', '217', '218'])).
% 51.72/51.93  thf('220', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['130', '131', '219'])).
% 51.72/51.93  thf('221', plain,
% 51.72/51.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 51.72/51.93      inference('demod', [status(thm)], ['185', '186', '187'])).
% 51.72/51.93  thf('222', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_B))
% 51.72/51.93         = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['220', '221'])).
% 51.72/51.93  thf('223', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('224', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['60'])).
% 51.72/51.93  thf('225', plain,
% 51.72/51.93      (![X23 : $i, X24 : $i]:
% 51.72/51.93         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('226', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['224', '225'])).
% 51.72/51.93  thf('227', plain,
% 51.72/51.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 51.72/51.93         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k4_xboole_0 @ X3 @ X5) @ X4))),
% 51.72/51.93      inference('cnf', [status(esa)], [t109_xboole_1])).
% 51.72/51.93  thf('228', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ 
% 51.72/51.93             (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['226', '227'])).
% 51.72/51.93  thf('229', plain,
% 51.72/51.93      (![X0 : $i, X2 : $i]:
% 51.72/51.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 51.72/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.72/51.93  thf('230', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 51.72/51.93               (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1))
% 51.72/51.93          | ((u1_struct_0 @ X0) = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['228', '229'])).
% 51.72/51.93  thf('231', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (r1_tarski @ (k2_struct_0 @ X0) @ 
% 51.72/51.93             (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((u1_struct_0 @ X0) = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['223', '230'])).
% 51.72/51.93  thf('232', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0) = (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (r1_tarski @ (k2_struct_0 @ X0) @ 
% 51.72/51.93               (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 51.72/51.93      inference('simplify', [status(thm)], ['231'])).
% 51.72/51.93  thf('233', plain,
% 51.72/51.93      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 51.72/51.93        | ~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | ((u1_struct_0 @ sk_A)
% 51.72/51.93            = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_B))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['222', '232'])).
% 51.72/51.93  thf('234', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 51.72/51.93      inference('simplify', [status(thm)], ['22'])).
% 51.72/51.93  thf('235', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('236', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_B))
% 51.72/51.93         = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['220', '221'])).
% 51.72/51.93  thf('237', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('238', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('239', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('240', plain,
% 51.72/51.93      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['14', '17'])).
% 51.72/51.93  thf('241', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('242', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('243', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('244', plain,
% 51.72/51.93      (![X27 : $i, X28 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X27)
% 51.72/51.93          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 51.72/51.93          | (m1_subset_1 @ (k2_pre_topc @ X27 @ X28) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 51.72/51.93  thf('245', plain,
% 51.72/51.93      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.72/51.93        | ~ (l1_pre_topc @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['243', '244'])).
% 51.72/51.93  thf('246', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('247', plain,
% 51.72/51.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['245', '246'])).
% 51.72/51.93  thf('248', plain,
% 51.72/51.93      (![X23 : $i, X24 : $i]:
% 51.72/51.93         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('249', plain,
% 51.72/51.93      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['247', '248'])).
% 51.72/51.93  thf('250', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('251', plain,
% 51.72/51.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['245', '246'])).
% 51.72/51.93  thf('252', plain,
% 51.72/51.93      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['250', '251'])).
% 51.72/51.93  thf('253', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('254', plain,
% 51.72/51.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['252', '253'])).
% 51.72/51.93  thf('255', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('256', plain,
% 51.72/51.93      (![X43 : $i, X44 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 51.72/51.93          | (r1_tarski @ (k1_tops_1 @ X44 @ X43) @ X43)
% 51.72/51.93          | ~ (l1_pre_topc @ X44))),
% 51.72/51.93      inference('cnf', [status(esa)], [t44_tops_1])).
% 51.72/51.93  thf('257', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (k1_tops_1 @ X0 @ X1) @ X1))),
% 51.72/51.93      inference('sup-', [status(thm)], ['255', '256'])).
% 51.72/51.93  thf('258', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((r1_tarski @ (k1_tops_1 @ X0 @ X1) @ X1)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['257'])).
% 51.72/51.93  thf('259', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 51.72/51.93           (k2_pre_topc @ sk_A @ sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['254', '258'])).
% 51.72/51.93  thf('260', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('261', plain,
% 51.72/51.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['245', '246'])).
% 51.72/51.93  thf(t84_tops_1, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( ( v2_tops_1 @ B @ A ) <=>
% 51.72/51.93             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 51.72/51.93  thf('262', plain,
% 51.72/51.93      (![X45 : $i, X46 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 51.72/51.93          | ~ (v2_tops_1 @ X45 @ X46)
% 51.72/51.93          | ((k1_tops_1 @ X46 @ X45) = (k1_xboole_0))
% 51.72/51.93          | ~ (l1_pre_topc @ X46))),
% 51.72/51.93      inference('cnf', [status(esa)], [t84_tops_1])).
% 51.72/51.93  thf('263', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 51.72/51.93        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['261', '262'])).
% 51.72/51.93  thf('264', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('265', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf(d5_tops_1, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( ( v3_tops_1 @ B @ A ) <=>
% 51.72/51.93             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 51.72/51.93  thf('266', plain,
% 51.72/51.93      (![X41 : $i, X42 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 51.72/51.93          | ~ (v3_tops_1 @ X41 @ X42)
% 51.72/51.93          | (v2_tops_1 @ (k2_pre_topc @ X42 @ X41) @ X42)
% 51.72/51.93          | ~ (l1_pre_topc @ X42))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_tops_1])).
% 51.72/51.93  thf('267', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 51.72/51.93        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['265', '266'])).
% 51.72/51.93  thf('268', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('269', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('270', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 51.72/51.93      inference('demod', [status(thm)], ['267', '268', '269'])).
% 51.72/51.93  thf('271', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['263', '264', '270'])).
% 51.72/51.93  thf('272', plain, ((r1_tarski @ k1_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['259', '260', '271'])).
% 51.72/51.93  thf('273', plain,
% 51.72/51.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 51.72/51.93         (~ (r1_tarski @ X6 @ X7)
% 51.72/51.93          | ~ (r1_tarski @ X7 @ X8)
% 51.72/51.93          | (r1_tarski @ X6 @ X8))),
% 51.72/51.93      inference('cnf', [status(esa)], [t1_xboole_1])).
% 51.72/51.93  thf('274', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((r1_tarski @ k1_xboole_0 @ X0)
% 51.72/51.93          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['272', '273'])).
% 51.72/51.93  thf('275', plain, ((r1_tarski @ k1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['249', '274'])).
% 51.72/51.93  thf('276', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('277', plain,
% 51.72/51.93      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['275', '276'])).
% 51.72/51.93  thf('278', plain,
% 51.72/51.93      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['242', '277'])).
% 51.72/51.93  thf('279', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('280', plain,
% 51.72/51.93      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['278', '279'])).
% 51.72/51.93  thf('281', plain,
% 51.72/51.93      (![X15 : $i, X16 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 51.72/51.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 51.72/51.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.72/51.93  thf('282', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['280', '281'])).
% 51.72/51.93  thf('283', plain,
% 51.72/51.93      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['278', '279'])).
% 51.72/51.93  thf('284', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('285', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['283', '284'])).
% 51.72/51.93  thf('286', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf('287', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['282', '285', '286'])).
% 51.72/51.93  thf('288', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.72/51.93           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1)))
% 51.72/51.93           = (k4_xboole_0 @ X1 @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['124', '127', '128'])).
% 51.72/51.93  thf('289', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.72/51.93           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1)))
% 51.72/51.93           = (k4_xboole_0 @ X1 @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['124', '127', '128'])).
% 51.72/51.93  thf('290', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 51.72/51.93           (k4_xboole_0 @ 
% 51.72/51.93            (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 51.72/51.93             (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X0))) @ 
% 51.72/51.93            (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))))
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup+', [status(thm)], ['288', '289'])).
% 51.72/51.93  thf('291', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 51.72/51.93           (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X1)))
% 51.72/51.93           = (k4_xboole_0 @ X1 @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['124', '127', '128'])).
% 51.72/51.93  thf('292', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ X1 @ X1)
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['169', '172'])).
% 51.72/51.93  thf('293', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ X1 @ X1)
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['169', '172'])).
% 51.72/51.93  thf('294', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ X0 @ X0)
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('demod', [status(thm)], ['290', '291', '292', '293'])).
% 51.72/51.93  thf('295', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 51.72/51.93         = (k4_xboole_0 @ k1_xboole_0 @ 
% 51.72/51.93            (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93             (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0))))),
% 51.72/51.93      inference('sup+', [status(thm)], ['287', '294'])).
% 51.72/51.93  thf('296', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['130', '131', '219'])).
% 51.72/51.93  thf('297', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)) = (k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['282', '285', '286'])).
% 51.72/51.93  thf('298', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['295', '296', '297'])).
% 51.72/51.93  thf('299', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 51.72/51.93          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['193', '194'])).
% 51.72/51.93  thf(d1_tops_1, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( ( k1_tops_1 @ A @ B ) =
% 51.72/51.93             ( k3_subset_1 @
% 51.72/51.93               ( u1_struct_0 @ A ) @ 
% 51.72/51.93               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 51.72/51.93  thf('300', plain,
% 51.72/51.93      (![X35 : $i, X36 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 51.72/51.93          | ((k1_tops_1 @ X36 @ X35)
% 51.72/51.93              = (k3_subset_1 @ (u1_struct_0 @ X36) @ 
% 51.72/51.93                 (k2_pre_topc @ X36 @ (k3_subset_1 @ (u1_struct_0 @ X36) @ X35))))
% 51.72/51.93          | ~ (l1_pre_topc @ X36))),
% 51.72/51.93      inference('cnf', [status(esa)], [d1_tops_1])).
% 51.72/51.93  thf('301', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ sk_A)
% 51.72/51.93          | ((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 51.72/51.93              = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93                 (k2_pre_topc @ sk_A @ 
% 51.72/51.93                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93                   (k4_xboole_0 @ sk_B @ X0))))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['299', '300'])).
% 51.72/51.93  thf('302', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('303', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0))
% 51.72/51.93           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['198', '199'])).
% 51.72/51.93  thf('304', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 51.72/51.93           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93              (k2_pre_topc @ sk_A @ 
% 51.72/51.93               (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0)))))),
% 51.72/51.93      inference('demod', [status(thm)], ['301', '302', '303'])).
% 51.72/51.93  thf('305', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('306', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('307', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 51.72/51.93           = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93              (k2_pre_topc @ sk_A @ 
% 51.72/51.93               (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ X0)))))),
% 51.72/51.93      inference('demod', [status(thm)], ['304', '305', '306'])).
% 51.72/51.93  thf('308', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 51.72/51.93         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93            (k2_pre_topc @ sk_A @ 
% 51.72/51.93             (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93              (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))))),
% 51.72/51.93      inference('sup+', [status(thm)], ['298', '307'])).
% 51.72/51.93  thf('309', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['295', '296', '297'])).
% 51.72/51.93  thf('310', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['130', '131', '219'])).
% 51.72/51.93  thf('311', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('312', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('313', plain,
% 51.72/51.93      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 51.72/51.93      inference('demod', [status(thm)], ['185', '186', '187'])).
% 51.72/51.93  thf('314', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['81', '82'])).
% 51.72/51.93  thf(d4_tops_1, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( ( v2_tops_1 @ B @ A ) <=>
% 51.72/51.93             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 51.72/51.93  thf('315', plain,
% 51.72/51.93      (![X39 : $i, X40 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 51.72/51.93          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X40) @ X39) @ X40)
% 51.72/51.93          | (v2_tops_1 @ X39 @ X40)
% 51.72/51.93          | ~ (l1_pre_topc @ X40))),
% 51.72/51.93      inference('cnf', [status(esa)], [d4_tops_1])).
% 51.72/51.93  thf('316', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (v2_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 51.72/51.93          | ~ (v1_tops_1 @ 
% 51.72/51.93               (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 51.72/51.93               X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['314', '315'])).
% 51.72/51.93  thf('317', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf('318', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (v2_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 51.72/51.93          | ~ (v1_tops_1 @ 
% 51.72/51.93               (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 51.72/51.93                (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 51.72/51.93               X0))),
% 51.72/51.93      inference('demod', [status(thm)], ['316', '317'])).
% 51.72/51.93  thf('319', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 51.72/51.93          | (v2_tops_1 @ 
% 51.72/51.93             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['313', '318'])).
% 51.72/51.93  thf('320', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('simplify', [status(thm)], ['35'])).
% 51.72/51.93  thf('321', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['23', '24'])).
% 51.72/51.93  thf(d3_tops_1, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( ( v1_tops_1 @ B @ A ) <=>
% 51.72/51.93             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 51.72/51.93  thf('322', plain,
% 51.72/51.93      (![X37 : $i, X38 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 51.72/51.93          | ((k2_pre_topc @ X38 @ X37) != (k2_struct_0 @ X38))
% 51.72/51.93          | (v1_tops_1 @ X37 @ X38)
% 51.72/51.93          | ~ (l1_pre_topc @ X38))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_tops_1])).
% 51.72/51.93  thf('323', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 51.72/51.93          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) != (k2_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['321', '322'])).
% 51.72/51.93  thf('324', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0) != (k2_struct_0 @ X0))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['320', '323'])).
% 51.72/51.93  thf('325', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((u1_struct_0 @ X0) != (k2_struct_0 @ X0)))),
% 51.72/51.93      inference('simplify', [status(thm)], ['324'])).
% 51.72/51.93  thf('326', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('327', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 51.72/51.93      inference('clc', [status(thm)], ['325', '326'])).
% 51.72/51.93  thf('328', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (v2_tops_1 @ 
% 51.72/51.93             (k4_xboole_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 51.72/51.93      inference('clc', [status(thm)], ['319', '327'])).
% 51.72/51.93  thf('329', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((v2_tops_1 @ 
% 51.72/51.93           (k4_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup+', [status(thm)], ['312', '328'])).
% 51.72/51.93  thf('330', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (v2_tops_1 @ 
% 51.72/51.93             (k4_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 51.72/51.93      inference('simplify', [status(thm)], ['329'])).
% 51.72/51.93  thf('331', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         ((v2_tops_1 @ 
% 51.72/51.93           (k4_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup+', [status(thm)], ['311', '330'])).
% 51.72/51.93  thf('332', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (v2_tops_1 @ 
% 51.72/51.93             (k4_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ X0))),
% 51.72/51.93      inference('simplify', [status(thm)], ['331'])).
% 51.72/51.93  thf('333', plain,
% 51.72/51.93      (((v2_tops_1 @ (k4_xboole_0 @ sk_B @ sk_B) @ sk_A)
% 51.72/51.93        | ~ (l1_pre_topc @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['310', '332'])).
% 51.72/51.93  thf('334', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('335', plain, ((v2_tops_1 @ (k4_xboole_0 @ sk_B @ sk_B) @ sk_A)),
% 51.72/51.93      inference('demod', [status(thm)], ['333', '334'])).
% 51.72/51.93  thf('336', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 51.72/51.93          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['193', '194'])).
% 51.72/51.93  thf('337', plain,
% 51.72/51.93      (![X45 : $i, X46 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 51.72/51.93          | ~ (v2_tops_1 @ X45 @ X46)
% 51.72/51.93          | ((k1_tops_1 @ X46 @ X45) = (k1_xboole_0))
% 51.72/51.93          | ~ (l1_pre_topc @ X46))),
% 51.72/51.93      inference('cnf', [status(esa)], [t84_tops_1])).
% 51.72/51.93  thf('338', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ sk_A)
% 51.72/51.93          | ((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))
% 51.72/51.93          | ~ (v2_tops_1 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['336', '337'])).
% 51.72/51.93  thf('339', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('340', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))
% 51.72/51.93          | ~ (v2_tops_1 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['338', '339'])).
% 51.72/51.93  thf('341', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B)) = (k1_xboole_0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['335', '340'])).
% 51.72/51.93  thf('342', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['295', '296', '297'])).
% 51.72/51.93  thf('343', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 51.72/51.93         = (k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['341', '342'])).
% 51.72/51.93  thf('344', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_B))
% 51.72/51.93         = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['220', '221'])).
% 51.72/51.93  thf('345', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['295', '296', '297'])).
% 51.72/51.93  thf('346', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['344', '345'])).
% 51.72/51.93  thf('347', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('348', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('simplify', [status(thm)], ['35'])).
% 51.72/51.93  thf('349', plain,
% 51.72/51.93      ((((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)))
% 51.72/51.93        | ~ (l1_pre_topc @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['347', '348'])).
% 51.72/51.93  thf('350', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('351', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('352', plain,
% 51.72/51.93      (((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['349', '350', '351'])).
% 51.72/51.93  thf('353', plain,
% 51.72/51.93      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['113', '114'])).
% 51.72/51.93  thf('354', plain,
% 51.72/51.93      (((k1_xboole_0)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)],
% 51.72/51.93                ['308', '309', '343', '346', '352', '353'])).
% 51.72/51.93  thf('355', plain,
% 51.72/51.93      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93           (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 51.72/51.93        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)],
% 51.72/51.93                ['96', '237', '238', '239', '240', '241', '354'])).
% 51.72/51.93  thf('356', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 51.72/51.93      inference('demod', [status(thm)], ['6', '7'])).
% 51.72/51.93  thf('357', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('358', plain,
% 51.72/51.93      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['356', '357'])).
% 51.72/51.93  thf('359', plain,
% 51.72/51.93      (![X15 : $i, X16 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 51.72/51.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 51.72/51.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.72/51.93  thf('360', plain,
% 51.72/51.93      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 51.72/51.93         = (k1_tops_1 @ sk_A @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['358', '359'])).
% 51.72/51.93  thf('361', plain,
% 51.72/51.93      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['356', '357'])).
% 51.72/51.93  thf('362', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('363', plain,
% 51.72/51.93      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 51.72/51.93         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['361', '362'])).
% 51.72/51.93  thf('364', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 51.72/51.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['83', '84'])).
% 51.72/51.93  thf('365', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 51.72/51.93         = (k1_tops_1 @ sk_A @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['360', '363', '364'])).
% 51.72/51.93  thf('366', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X1))),
% 51.72/51.93      inference('demod', [status(thm)], ['117', '118', '119'])).
% 51.72/51.93  thf('367', plain,
% 51.72/51.93      ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))),
% 51.72/51.93      inference('sup+', [status(thm)], ['365', '366'])).
% 51.72/51.93  thf('368', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['295', '296', '297'])).
% 51.72/51.93  thf('369', plain,
% 51.72/51.93      ((r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 51.72/51.93        (k1_tops_1 @ sk_A @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['367', '368'])).
% 51.72/51.93  thf('370', plain,
% 51.72/51.93      (((k1_xboole_0)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)],
% 51.72/51.93                ['308', '309', '343', '346', '352', '353'])).
% 51.72/51.93  thf('371', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_B))
% 51.72/51.93         = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['220', '221'])).
% 51.72/51.93  thf('372', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((k4_xboole_0 @ X0 @ X0)
% 51.72/51.93           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 51.72/51.93      inference('demod', [status(thm)], ['290', '291', '292', '293'])).
% 51.72/51.93  thf('373', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93            (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_B))))),
% 51.72/51.93      inference('sup+', [status(thm)], ['371', '372'])).
% 51.72/51.93  thf('374', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['130', '131', '219'])).
% 51.72/51.93  thf('375', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k4_xboole_0 @ sk_B @ sk_B))
% 51.72/51.93         = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['220', '221'])).
% 51.72/51.93  thf('376', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['373', '374', '375'])).
% 51.72/51.93  thf('377', plain,
% 51.72/51.93      (((k4_xboole_0 @ sk_B @ sk_B) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 51.72/51.93      inference('demod', [status(thm)], ['295', '296', '297'])).
% 51.72/51.93  thf('378', plain,
% 51.72/51.93      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['376', '377'])).
% 51.72/51.93  thf('379', plain,
% 51.72/51.93      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 51.72/51.93      inference('sup+', [status(thm)], ['370', '378'])).
% 51.72/51.93  thf('380', plain, ((r1_tarski @ k1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['369', '379'])).
% 51.72/51.93  thf('381', plain,
% 51.72/51.93      (![X0 : $i, X2 : $i]:
% 51.72/51.93         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 51.72/51.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 51.72/51.93  thf('382', plain,
% 51.72/51.93      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 51.72/51.93        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['380', '381'])).
% 51.72/51.93  thf('383', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('384', plain,
% 51.72/51.93      (![X45 : $i, X46 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 51.72/51.93          | ((k1_tops_1 @ X46 @ X45) != (k1_xboole_0))
% 51.72/51.93          | (v2_tops_1 @ X45 @ X46)
% 51.72/51.93          | ~ (l1_pre_topc @ X46))),
% 51.72/51.93      inference('cnf', [status(esa)], [t84_tops_1])).
% 51.72/51.93  thf('385', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | (v2_tops_1 @ sk_B @ sk_A)
% 51.72/51.93        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['383', '384'])).
% 51.72/51.93  thf('386', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('387', plain,
% 51.72/51.93      (((v2_tops_1 @ sk_B @ sk_A)
% 51.72/51.93        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 51.72/51.93      inference('demod', [status(thm)], ['385', '386'])).
% 51.72/51.93  thf('388', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('389', plain,
% 51.72/51.93      (![X39 : $i, X40 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 51.72/51.93          | ~ (v2_tops_1 @ X39 @ X40)
% 51.72/51.93          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X40) @ X39) @ X40)
% 51.72/51.93          | ~ (l1_pre_topc @ X40))),
% 51.72/51.93      inference('cnf', [status(esa)], [d4_tops_1])).
% 51.72/51.93  thf('390', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 51.72/51.93        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['388', '389'])).
% 51.72/51.93  thf('391', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('392', plain,
% 51.72/51.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['142', '149'])).
% 51.72/51.93  thf('393', plain,
% 51.72/51.93      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 51.72/51.93        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['390', '391', '392'])).
% 51.72/51.93  thf('394', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('395', plain,
% 51.72/51.93      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('396', plain,
% 51.72/51.93      ((~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['394', '395'])).
% 51.72/51.93  thf('397', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('398', plain,
% 51.72/51.93      (~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 51.72/51.93      inference('demod', [status(thm)], ['396', '397'])).
% 51.72/51.93  thf('399', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['104', '105'])).
% 51.72/51.93  thf('400', plain,
% 51.72/51.93      (~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 51.72/51.93      inference('demod', [status(thm)], ['398', '399'])).
% 51.72/51.93  thf('401', plain, (~ (v2_tops_1 @ sk_B @ sk_A)),
% 51.72/51.93      inference('clc', [status(thm)], ['393', '400'])).
% 51.72/51.93  thf('402', plain, (((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 51.72/51.93      inference('clc', [status(thm)], ['387', '401'])).
% 51.72/51.93  thf('403', plain, (~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 51.72/51.93      inference('simplify_reflect-', [status(thm)], ['382', '402'])).
% 51.72/51.93  thf('404', plain,
% 51.72/51.93      (~ (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 51.72/51.93      inference('clc', [status(thm)], ['355', '403'])).
% 51.72/51.93  thf('405', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ 
% 51.72/51.93             (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['226', '227'])).
% 51.72/51.93  thf('406', plain,
% 51.72/51.93      (![X23 : $i, X25 : $i]:
% 51.72/51.93         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 51.72/51.93      inference('cnf', [status(esa)], [t3_subset])).
% 51.72/51.93  thf('407', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | (m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['405', '406'])).
% 51.72/51.93  thf('408', plain,
% 51.72/51.93      (![X43 : $i, X44 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 51.72/51.93          | (r1_tarski @ (k1_tops_1 @ X44 @ X43) @ X43)
% 51.72/51.93          | ~ (l1_pre_topc @ X44))),
% 51.72/51.93      inference('cnf', [status(esa)], [t44_tops_1])).
% 51.72/51.93  thf('409', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | (r1_tarski @ 
% 51.72/51.93             (k1_tops_1 @ X0 @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)) @ 
% 51.72/51.93             (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['407', '408'])).
% 51.72/51.93  thf('410', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((r1_tarski @ 
% 51.72/51.93           (k1_tops_1 @ X0 @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1)) @ 
% 51.72/51.93           (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('simplify', [status(thm)], ['409'])).
% 51.72/51.93  thf('411', plain,
% 51.72/51.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['252', '253'])).
% 51.72/51.93  thf('412', plain,
% 51.72/51.93      (![X13 : $i, X14 : $i]:
% 51.72/51.93         ((m1_subset_1 @ (k3_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 51.72/51.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 51.72/51.93  thf('413', plain,
% 51.72/51.93      ((m1_subset_1 @ 
% 51.72/51.93        (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['411', '412'])).
% 51.72/51.93  thf('414', plain,
% 51.72/51.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['252', '253'])).
% 51.72/51.93  thf('415', plain,
% 51.72/51.93      (![X11 : $i, X12 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 51.72/51.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 51.72/51.93      inference('cnf', [status(esa)], [d5_subset_1])).
% 51.72/51.93  thf('416', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['414', '415'])).
% 51.72/51.93  thf('417', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf('418', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['147', '148'])).
% 51.72/51.93  thf('419', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['81', '82'])).
% 51.72/51.93  thf('420', plain,
% 51.72/51.93      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('sup+', [status(thm)], ['418', '419'])).
% 51.72/51.93  thf('421', plain,
% 51.72/51.93      (![X35 : $i, X36 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 51.72/51.93          | ((k1_tops_1 @ X36 @ X35)
% 51.72/51.93              = (k3_subset_1 @ (u1_struct_0 @ X36) @ 
% 51.72/51.93                 (k2_pre_topc @ X36 @ (k3_subset_1 @ (u1_struct_0 @ X36) @ X35))))
% 51.72/51.93          | ~ (l1_pre_topc @ X36))),
% 51.72/51.93      inference('cnf', [status(esa)], [d1_tops_1])).
% 51.72/51.93  thf('422', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | ((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 51.72/51.93            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93               (k2_pre_topc @ sk_A @ 
% 51.72/51.93                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93                 (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['420', '421'])).
% 51.72/51.93  thf('423', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('424', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('425', plain,
% 51.72/51.93      (![X15 : $i, X16 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 51.72/51.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 51.72/51.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.72/51.93  thf('426', plain,
% 51.72/51.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.72/51.93      inference('sup-', [status(thm)], ['424', '425'])).
% 51.72/51.93  thf('427', plain,
% 51.72/51.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['142', '149'])).
% 51.72/51.93  thf('428', plain,
% 51.72/51.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['426', '427'])).
% 51.72/51.93  thf('429', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 51.72/51.93         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 51.72/51.93      inference('demod', [status(thm)], ['422', '423', '428'])).
% 51.72/51.93  thf('430', plain,
% 51.72/51.93      ((((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 51.72/51.93          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 51.72/51.93        | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['417', '429'])).
% 51.72/51.93  thf('431', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['414', '415'])).
% 51.72/51.93  thf('432', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('433', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 51.72/51.93      inference('demod', [status(thm)], ['430', '431', '432'])).
% 51.72/51.93  thf('434', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 51.72/51.93         = (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 51.72/51.93      inference('demod', [status(thm)], ['416', '433'])).
% 51.72/51.93  thf('435', plain,
% 51.72/51.93      ((m1_subset_1 @ 
% 51.72/51.93        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['413', '434'])).
% 51.72/51.93  thf('436', plain,
% 51.72/51.93      (![X26 : $i]:
% 51.72/51.93         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_struct_0])).
% 51.72/51.93  thf(t49_pre_topc, axiom,
% 51.72/51.93    (![A:$i]:
% 51.72/51.93     ( ( l1_pre_topc @ A ) =>
% 51.72/51.93       ( ![B:$i]:
% 51.72/51.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93           ( ![C:$i]:
% 51.72/51.93             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 51.72/51.93               ( ( r1_tarski @ B @ C ) =>
% 51.72/51.93                 ( r1_tarski @
% 51.72/51.93                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 51.72/51.93  thf('437', plain,
% 51.72/51.93      (![X32 : $i, X33 : $i, X34 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.72/51.93          | ~ (r1_tarski @ X32 @ X34)
% 51.72/51.93          | (r1_tarski @ (k2_pre_topc @ X33 @ X32) @ (k2_pre_topc @ X33 @ X34))
% 51.72/51.93          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 51.72/51.93          | ~ (l1_pre_topc @ X33))),
% 51.72/51.93      inference('cnf', [status(esa)], [t49_pre_topc])).
% 51.72/51.93  thf('438', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_struct_0 @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | (r1_tarski @ (k2_pre_topc @ X0 @ X1) @ (k2_pre_topc @ X0 @ X2))
% 51.72/51.93          | ~ (r1_tarski @ X1 @ X2))),
% 51.72/51.93      inference('sup-', [status(thm)], ['436', '437'])).
% 51.72/51.93  thf('439', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (r1_tarski @ 
% 51.72/51.93             (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93             X0)
% 51.72/51.93          | (r1_tarski @ 
% 51.72/51.93             (k2_pre_topc @ sk_A @ 
% 51.72/51.93              (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))) @ 
% 51.72/51.93             (k2_pre_topc @ sk_A @ X0))
% 51.72/51.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.72/51.93          | ~ (l1_pre_topc @ sk_A)
% 51.72/51.93          | ~ (l1_struct_0 @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['435', '438'])).
% 51.72/51.93  thf('440', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('441', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('442', plain, ((l1_struct_0 @ sk_A)),
% 51.72/51.93      inference('sup-', [status(thm)], ['15', '16'])).
% 51.72/51.93  thf('443', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (r1_tarski @ 
% 51.72/51.93             (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93             X0)
% 51.72/51.93          | (r1_tarski @ 
% 51.72/51.93             (k2_pre_topc @ sk_A @ 
% 51.72/51.93              (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))) @ 
% 51.72/51.93             (k2_pre_topc @ sk_A @ X0))
% 51.72/51.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 51.72/51.93      inference('demod', [status(thm)], ['439', '440', '441', '442'])).
% 51.72/51.93  thf('444', plain,
% 51.72/51.93      ((m1_subset_1 @ 
% 51.72/51.93        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['413', '434'])).
% 51.72/51.93  thf('445', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('446', plain,
% 51.72/51.93      (![X37 : $i, X38 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 51.72/51.93          | ~ (v1_tops_1 @ X37 @ X38)
% 51.72/51.93          | ((k2_pre_topc @ X38 @ X37) = (k2_struct_0 @ X38))
% 51.72/51.93          | ~ (l1_pre_topc @ X38))),
% 51.72/51.93      inference('cnf', [status(esa)], [d3_tops_1])).
% 51.72/51.93  thf('447', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ((k2_pre_topc @ X0 @ X1) = (k2_struct_0 @ X0))
% 51.72/51.93          | ~ (v1_tops_1 @ X1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['445', '446'])).
% 51.72/51.93  thf('448', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (v1_tops_1 @ X1 @ X0)
% 51.72/51.93          | ((k2_pre_topc @ X0 @ X1) = (k2_struct_0 @ X0))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['447'])).
% 51.72/51.93  thf('449', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | ((k2_pre_topc @ sk_A @ 
% 51.72/51.93            (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 51.72/51.93            = (k2_struct_0 @ sk_A))
% 51.72/51.93        | ~ (v1_tops_1 @ 
% 51.72/51.93             (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93             sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['444', '448'])).
% 51.72/51.93  thf('450', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('451', plain,
% 51.72/51.93      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['252', '253'])).
% 51.72/51.93  thf('452', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 51.72/51.93      inference('clc', [status(thm)], ['50', '51'])).
% 51.72/51.93  thf('453', plain,
% 51.72/51.93      (![X39 : $i, X40 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 51.72/51.93          | ~ (v2_tops_1 @ X39 @ X40)
% 51.72/51.93          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X40) @ X39) @ X40)
% 51.72/51.93          | ~ (l1_pre_topc @ X40))),
% 51.72/51.93      inference('cnf', [status(esa)], [d4_tops_1])).
% 51.72/51.93  thf('454', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 51.72/51.93          | ~ (v2_tops_1 @ X1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['452', '453'])).
% 51.72/51.93  thf('455', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (~ (v2_tops_1 @ X1 @ X0)
% 51.72/51.93          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 51.72/51.93          | ~ (l1_pre_topc @ X0)
% 51.72/51.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 51.72/51.93      inference('simplify', [status(thm)], ['454'])).
% 51.72/51.93  thf('456', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | (v1_tops_1 @ 
% 51.72/51.93           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 51.72/51.93           sk_A)
% 51.72/51.93        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 51.72/51.93      inference('sup-', [status(thm)], ['451', '455'])).
% 51.72/51.93  thf('457', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('458', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 51.72/51.93         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 51.72/51.93      inference('demod', [status(thm)], ['422', '423', '428'])).
% 51.72/51.93  thf('459', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 51.72/51.93      inference('demod', [status(thm)], ['267', '268', '269'])).
% 51.72/51.93  thf('460', plain,
% 51.72/51.93      ((v1_tops_1 @ 
% 51.72/51.93        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ sk_A)),
% 51.72/51.93      inference('demod', [status(thm)], ['456', '457', '458', '459'])).
% 51.72/51.93  thf('461', plain,
% 51.72/51.93      (((k2_pre_topc @ sk_A @ 
% 51.72/51.93         (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 51.72/51.93         = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['449', '450', '460'])).
% 51.72/51.93  thf('462', plain,
% 51.72/51.93      (![X0 : $i]:
% 51.72/51.93         (~ (r1_tarski @ 
% 51.72/51.93             (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93             X0)
% 51.72/51.93          | (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 51.72/51.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 51.72/51.93      inference('demod', [status(thm)], ['443', '461'])).
% 51.72/51.93  thf('463', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | ~ (m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 51.72/51.93        | (r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['410', '462'])).
% 51.72/51.93  thf('464', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('465', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['81', '82'])).
% 51.72/51.93  thf('466', plain,
% 51.72/51.93      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['147', '148'])).
% 51.72/51.93  thf('467', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['81', '82'])).
% 51.72/51.93  thf('468', plain,
% 51.72/51.93      (![X27 : $i, X28 : $i]:
% 51.72/51.93         (~ (l1_pre_topc @ X27)
% 51.72/51.93          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 51.72/51.93          | (m1_subset_1 @ (k2_pre_topc @ X27 @ X28) @ 
% 51.72/51.93             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 51.72/51.93      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 51.72/51.93  thf('469', plain,
% 51.72/51.93      (![X0 : $i, X1 : $i]:
% 51.72/51.93         ((m1_subset_1 @ 
% 51.72/51.93           (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 51.72/51.93           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 51.72/51.93          | ~ (l1_pre_topc @ X0))),
% 51.72/51.93      inference('sup-', [status(thm)], ['467', '468'])).
% 51.72/51.93  thf('470', plain,
% 51.72/51.93      (((m1_subset_1 @ 
% 51.72/51.93         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 51.72/51.93        | ~ (l1_pre_topc @ sk_A))),
% 51.72/51.93      inference('sup+', [status(thm)], ['466', '469'])).
% 51.72/51.93  thf('471', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('472', plain,
% 51.72/51.93      ((m1_subset_1 @ 
% 51.72/51.93        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['470', '471'])).
% 51.72/51.93  thf('473', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('474', plain,
% 51.72/51.93      ((m1_subset_1 @ 
% 51.72/51.93        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 51.72/51.93        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 51.72/51.93      inference('demod', [status(thm)], ['472', '473'])).
% 51.72/51.93  thf('475', plain,
% 51.72/51.93      (![X15 : $i, X16 : $i]:
% 51.72/51.93         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 51.72/51.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 51.72/51.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 51.72/51.93  thf('476', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 51.72/51.93         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['474', '475'])).
% 51.72/51.93  thf('477', plain,
% 51.72/51.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('478', plain,
% 51.72/51.93      (![X35 : $i, X36 : $i]:
% 51.72/51.93         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 51.72/51.93          | ((k1_tops_1 @ X36 @ X35)
% 51.72/51.93              = (k3_subset_1 @ (u1_struct_0 @ X36) @ 
% 51.72/51.93                 (k2_pre_topc @ X36 @ (k3_subset_1 @ (u1_struct_0 @ X36) @ X35))))
% 51.72/51.93          | ~ (l1_pre_topc @ X36))),
% 51.72/51.93      inference('cnf', [status(esa)], [d1_tops_1])).
% 51.72/51.93  thf('479', plain,
% 51.72/51.93      ((~ (l1_pre_topc @ sk_A)
% 51.72/51.93        | ((k1_tops_1 @ sk_A @ sk_B)
% 51.72/51.93            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93               (k2_pre_topc @ sk_A @ 
% 51.72/51.93                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 51.72/51.93      inference('sup-', [status(thm)], ['477', '478'])).
% 51.72/51.93  thf('480', plain, ((l1_pre_topc @ sk_A)),
% 51.72/51.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.72/51.93  thf('481', plain,
% 51.72/51.93      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 51.72/51.93      inference('demod', [status(thm)], ['142', '149'])).
% 51.72/51.93  thf('482', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ sk_B)
% 51.72/51.93         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 51.72/51.93            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 51.72/51.93      inference('demod', [status(thm)], ['479', '480', '481'])).
% 51.72/51.93  thf('483', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 51.72/51.93      inference('demod', [status(thm)], ['233', '234', '235', '236'])).
% 51.72/51.93  thf('484', plain,
% 51.72/51.93      (((k1_tops_1 @ sk_A @ sk_B)
% 51.72/51.93         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 51.72/51.93      inference('demod', [status(thm)], ['482', '483'])).
% 51.72/51.93  thf('485', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 51.72/51.93         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 51.72/51.93      inference('demod', [status(thm)], ['476', '484'])).
% 51.72/51.93  thf('486', plain,
% 51.72/51.93      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 51.72/51.93      inference('sup-', [status(thm)], ['18', '19'])).
% 51.72/51.93  thf('487', plain,
% 51.72/51.93      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 51.72/51.93         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 51.72/51.93      inference('sup+', [status(thm)], ['485', '486'])).
% 51.72/51.93  thf('488', plain,
% 51.72/51.93      ((r1_tarski @ (k2_struct_0 @ sk_A) @ 
% 51.72/51.93        (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 51.72/51.93      inference('demod', [status(thm)], ['463', '464', '465', '487'])).
% 51.72/51.93  thf('489', plain, ($false), inference('demod', [status(thm)], ['404', '488'])).
% 51.72/51.93  
% 51.72/51.93  % SZS output end Refutation
% 51.72/51.93  
% 51.72/51.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
