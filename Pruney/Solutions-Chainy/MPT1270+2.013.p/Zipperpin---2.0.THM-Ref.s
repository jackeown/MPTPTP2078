%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xuyi5KESBA

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:27 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 351 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :   18
%              Number of atoms          :  791 (3695 expanded)
%              Number of equality atoms :   36 (  89 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','23'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('39',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','23'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tops_1 @ X30 @ X31 )
      | ( ( k1_tops_1 @ X31 @ X30 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('46',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('47',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','36','46'])).

thf('48',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['45','47'])).

thf('49',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','48'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('51',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','49','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','51'])).

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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 @ ( k2_tops_1 @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','65'])).

thf('67',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','49','50'])).

thf('68',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('71',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['68','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['52','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xuyi5KESBA
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.41/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.57  % Solved by: fo/fo7.sh
% 0.41/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.57  % done 228 iterations in 0.123s
% 0.41/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.57  % SZS output start Refutation
% 0.41/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.41/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.41/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.41/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.41/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.57  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.41/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.41/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.57  thf(t88_tops_1, conjecture,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( l1_pre_topc @ A ) =>
% 0.41/0.57       ( ![B:$i]:
% 0.41/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.57           ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.57             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.57    (~( ![A:$i]:
% 0.41/0.57        ( ( l1_pre_topc @ A ) =>
% 0.41/0.57          ( ![B:$i]:
% 0.41/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.57              ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.57                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.41/0.57    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.41/0.57  thf('0', plain,
% 0.41/0.57      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('1', plain,
% 0.41/0.57      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.57         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.57      inference('split', [status(esa)], ['0'])).
% 0.41/0.57  thf('2', plain,
% 0.41/0.57      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.41/0.57       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.57      inference('split', [status(esa)], ['0'])).
% 0.41/0.57  thf('3', plain,
% 0.41/0.57      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.57        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('4', plain,
% 0.41/0.57      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.57         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.57      inference('split', [status(esa)], ['3'])).
% 0.41/0.57  thf('5', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t44_tops_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( l1_pre_topc @ A ) =>
% 0.41/0.57       ( ![B:$i]:
% 0.41/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.57           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.41/0.57  thf('6', plain,
% 0.41/0.57      (![X26 : $i, X27 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.41/0.57          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 0.41/0.57          | ~ (l1_pre_topc @ X27))),
% 0.41/0.57      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.41/0.57  thf('7', plain,
% 0.41/0.57      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.41/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.57  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('9', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.41/0.57      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.57  thf(t1_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.41/0.57       ( r1_tarski @ A @ C ) ))).
% 0.41/0.57  thf('10', plain,
% 0.41/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.57         (~ (r1_tarski @ X8 @ X9)
% 0.41/0.57          | ~ (r1_tarski @ X9 @ X10)
% 0.41/0.57          | (r1_tarski @ X8 @ X10))),
% 0.41/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.41/0.57  thf('11', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.41/0.57          | ~ (r1_tarski @ sk_B @ X0))),
% 0.41/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.57  thf('12', plain,
% 0.41/0.57      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.41/0.57         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['4', '11'])).
% 0.41/0.57  thf('13', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(l78_tops_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( l1_pre_topc @ A ) =>
% 0.41/0.57       ( ![B:$i]:
% 0.41/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.57           ( ( k2_tops_1 @ A @ B ) =
% 0.41/0.57             ( k7_subset_1 @
% 0.41/0.57               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.41/0.57               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.57  thf('14', plain,
% 0.41/0.57      (![X24 : $i, X25 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.57          | ((k2_tops_1 @ X25 @ X24)
% 0.41/0.57              = (k7_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.41/0.57                 (k2_pre_topc @ X25 @ X24) @ (k1_tops_1 @ X25 @ X24)))
% 0.41/0.57          | ~ (l1_pre_topc @ X25))),
% 0.41/0.57      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.41/0.57  thf('15', plain,
% 0.41/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.57        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.57               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.57  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('17', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(dt_k2_pre_topc, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.57       ( m1_subset_1 @
% 0.41/0.57         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.57  thf('18', plain,
% 0.41/0.57      (![X20 : $i, X21 : $i]:
% 0.41/0.57         (~ (l1_pre_topc @ X20)
% 0.41/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.41/0.57          | (m1_subset_1 @ (k2_pre_topc @ X20 @ X21) @ 
% 0.41/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.41/0.57      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.41/0.57  thf('19', plain,
% 0.41/0.57      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.57  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('21', plain,
% 0.41/0.57      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('demod', [status(thm)], ['19', '20'])).
% 0.41/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.41/0.57  thf('22', plain,
% 0.41/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.41/0.57          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.41/0.57  thf('23', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.57           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.41/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.57  thf('24', plain,
% 0.41/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.57         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.57            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.57      inference('demod', [status(thm)], ['15', '16', '23'])).
% 0.41/0.57  thf(t38_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.41/0.57       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.57  thf('25', plain,
% 0.41/0.57      (![X11 : $i, X12 : $i]:
% 0.41/0.57         (((X11) = (k1_xboole_0))
% 0.41/0.57          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 0.41/0.57      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.41/0.57  thf('26', plain,
% 0.41/0.57      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.57        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.57  thf('27', plain,
% 0.41/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.41/0.57         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['12', '26'])).
% 0.41/0.57  thf('28', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t84_tops_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( l1_pre_topc @ A ) =>
% 0.41/0.57       ( ![B:$i]:
% 0.41/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.57           ( ( v2_tops_1 @ B @ A ) <=>
% 0.41/0.57             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.41/0.57  thf('29', plain,
% 0.41/0.57      (![X30 : $i, X31 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.41/0.57          | ((k1_tops_1 @ X31 @ X30) != (k1_xboole_0))
% 0.41/0.57          | (v2_tops_1 @ X30 @ X31)
% 0.41/0.57          | ~ (l1_pre_topc @ X31))),
% 0.41/0.57      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.41/0.57  thf('30', plain,
% 0.41/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.57        | (v2_tops_1 @ sk_B @ sk_A)
% 0.41/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.57  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('32', plain,
% 0.41/0.57      (((v2_tops_1 @ sk_B @ sk_A)
% 0.41/0.57        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.41/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.57  thf('33', plain,
% 0.41/0.57      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.41/0.57         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['27', '32'])).
% 0.41/0.57  thf('34', plain,
% 0.41/0.57      (((v2_tops_1 @ sk_B @ sk_A))
% 0.41/0.57         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.41/0.57  thf('35', plain,
% 0.41/0.57      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.41/0.57      inference('split', [status(esa)], ['0'])).
% 0.41/0.57  thf('36', plain,
% 0.41/0.57      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.41/0.57       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.57  thf('37', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.57      inference('sat_resolution*', [status(thm)], ['2', '36'])).
% 0.41/0.57  thf('38', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.41/0.57      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 0.41/0.57  thf('39', plain,
% 0.41/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.41/0.57         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.41/0.57            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.57      inference('demod', [status(thm)], ['15', '16', '23'])).
% 0.41/0.57  thf('40', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('41', plain,
% 0.41/0.57      (![X30 : $i, X31 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.41/0.57          | ~ (v2_tops_1 @ X30 @ X31)
% 0.41/0.57          | ((k1_tops_1 @ X31 @ X30) = (k1_xboole_0))
% 0.41/0.57          | ~ (l1_pre_topc @ X31))),
% 0.41/0.57      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.41/0.57  thf('42', plain,
% 0.41/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.57        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.41/0.57  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('44', plain,
% 0.41/0.57      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.41/0.57        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.57      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.57  thf('45', plain,
% 0.41/0.57      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.41/0.57      inference('split', [status(esa)], ['3'])).
% 0.41/0.57  thf('46', plain,
% 0.41/0.57      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.41/0.57       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.57      inference('split', [status(esa)], ['3'])).
% 0.41/0.57  thf('47', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.41/0.57      inference('sat_resolution*', [status(thm)], ['2', '36', '46'])).
% 0.41/0.57  thf('48', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.41/0.57      inference('simpl_trail', [status(thm)], ['45', '47'])).
% 0.41/0.57  thf('49', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.41/0.57      inference('demod', [status(thm)], ['44', '48'])).
% 0.41/0.57  thf(t3_boole, axiom,
% 0.41/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.57  thf('50', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.41/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.41/0.57  thf('51', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.41/0.57      inference('demod', [status(thm)], ['39', '49', '50'])).
% 0.41/0.57  thf('52', plain, (~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.41/0.57      inference('demod', [status(thm)], ['38', '51'])).
% 0.41/0.57  thf('53', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(t65_tops_1, axiom,
% 0.41/0.57    (![A:$i]:
% 0.41/0.57     ( ( l1_pre_topc @ A ) =>
% 0.41/0.57       ( ![B:$i]:
% 0.41/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.57           ( ( k2_pre_topc @ A @ B ) =
% 0.41/0.57             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.41/0.57  thf('54', plain,
% 0.41/0.57      (![X28 : $i, X29 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.41/0.57          | ((k2_pre_topc @ X29 @ X28)
% 0.41/0.57              = (k4_subset_1 @ (u1_struct_0 @ X29) @ X28 @ 
% 0.41/0.57                 (k2_tops_1 @ X29 @ X28)))
% 0.41/0.57          | ~ (l1_pre_topc @ X29))),
% 0.41/0.57      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.41/0.57  thf('55', plain,
% 0.41/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.57        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.41/0.57            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.41/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.57  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('57', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(dt_k2_tops_1, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.57       ( m1_subset_1 @
% 0.41/0.57         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.57  thf('58', plain,
% 0.41/0.57      (![X22 : $i, X23 : $i]:
% 0.41/0.57         (~ (l1_pre_topc @ X22)
% 0.41/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.41/0.57          | (m1_subset_1 @ (k2_tops_1 @ X22 @ X23) @ 
% 0.41/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.41/0.57      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.41/0.57  thf('59', plain,
% 0.41/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.41/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.41/0.57      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.57  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf('61', plain,
% 0.41/0.57      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.41/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('demod', [status(thm)], ['59', '60'])).
% 0.41/0.57  thf('62', plain,
% 0.41/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.41/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.57  thf('63', plain,
% 0.41/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.41/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 0.41/0.57          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 0.41/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.41/0.57  thf('64', plain,
% 0.41/0.57      (![X0 : $i]:
% 0.41/0.57         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.41/0.57            = (k2_xboole_0 @ sk_B @ X0))
% 0.41/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.57  thf('65', plain,
% 0.41/0.57      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.41/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.57      inference('sup-', [status(thm)], ['61', '64'])).
% 0.41/0.57  thf('66', plain,
% 0.41/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.41/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.41/0.57      inference('demod', [status(thm)], ['55', '56', '65'])).
% 0.41/0.57  thf('67', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.41/0.57      inference('demod', [status(thm)], ['39', '49', '50'])).
% 0.41/0.57  thf('68', plain,
% 0.41/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.41/0.57         = (k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.41/0.57      inference('demod', [status(thm)], ['66', '67'])).
% 0.41/0.57  thf(d10_xboole_0, axiom,
% 0.41/0.57    (![A:$i,B:$i]:
% 0.41/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.57  thf('69', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.41/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.57  thf('70', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.41/0.57      inference('simplify', [status(thm)], ['69'])).
% 0.41/0.57  thf(t11_xboole_1, axiom,
% 0.41/0.57    (![A:$i,B:$i,C:$i]:
% 0.41/0.57     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.41/0.57  thf('71', plain,
% 0.41/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.57         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.41/0.57      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.41/0.57  thf('72', plain,
% 0.41/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.41/0.57      inference('sup-', [status(thm)], ['70', '71'])).
% 0.41/0.57  thf('73', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.41/0.57      inference('sup+', [status(thm)], ['68', '72'])).
% 0.41/0.57  thf('74', plain, ($false), inference('demod', [status(thm)], ['52', '73'])).
% 0.41/0.57  
% 0.41/0.57  % SZS output end Refutation
% 0.41/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
