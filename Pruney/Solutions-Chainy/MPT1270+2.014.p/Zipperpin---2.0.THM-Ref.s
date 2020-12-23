%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S6Uf5IubXG

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:27 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 224 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  824 (2179 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

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

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X38 @ X37 ) @ ( k2_tops_1 @ X38 @ X37 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X36 @ X35 ) @ X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('39',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ X31 @ ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ X33 ) @ ( k1_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v2_tops_1 @ X39 @ X40 )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('56',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','35','55'])).

thf('57',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['54','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('67',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('69',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','57','64','78'])).

thf('80',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['37','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S6Uf5IubXG
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 705 iterations in 0.248s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.52/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.52/0.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.52/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.71  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.52/0.71  thf(t88_tops_1, conjecture,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ( v2_tops_1 @ B @ A ) <=>
% 0.52/0.71             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i]:
% 0.52/0.71        ( ( l1_pre_topc @ A ) =>
% 0.52/0.71          ( ![B:$i]:
% 0.52/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71              ( ( v2_tops_1 @ B @ A ) <=>
% 0.52/0.71                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.52/0.71  thf('0', plain,
% 0.52/0.71      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.71        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 0.52/0.71       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t73_tops_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      (![X37 : $i, X38 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.52/0.71          | (r1_xboole_0 @ (k1_tops_1 @ X38 @ X37) @ (k2_tops_1 @ X38 @ X37))
% 0.52/0.71          | ~ (l1_pre_topc @ X38))),
% 0.52/0.71      inference('cnf', [status(esa)], [t73_tops_1])).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.71  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['5', '6'])).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.71        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('9', plain,
% 0.52/0.71      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('split', [status(esa)], ['8'])).
% 0.52/0.71  thf(t12_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      (![X3 : $i, X4 : $i]:
% 0.52/0.71         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.71  thf(t70_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.52/0.71            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.52/0.71       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.52/0.71            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.52/0.71         ((r1_xboole_0 @ X9 @ X10)
% 0.52/0.71          | ~ (r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      ((![X0 : $i]:
% 0.52/0.71          (~ (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.52/0.71           | (r1_xboole_0 @ X0 @ sk_B)))
% 0.52/0.71         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.52/0.71         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['7', '13'])).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t44_tops_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.52/0.71  thf('16', plain,
% 0.52/0.71      (![X35 : $i, X36 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.52/0.71          | (r1_tarski @ (k1_tops_1 @ X36 @ X35) @ X35)
% 0.52/0.71          | ~ (l1_pre_topc @ X36))),
% 0.52/0.71      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.71  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.52/0.71      inference('demod', [status(thm)], ['17', '18'])).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      (![X3 : $i, X4 : $i]:
% 0.52/0.71         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 0.52/0.71      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.52/0.71         ((r1_xboole_0 @ X9 @ X10)
% 0.52/0.71          | ~ (r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (r1_xboole_0 @ X0 @ sk_B)
% 0.52/0.71          | (r1_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.52/0.71         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['14', '23'])).
% 0.52/0.71  thf(t66_xboole_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.52/0.71       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X8))),
% 0.52/0.71      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.52/0.71         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t84_tops_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ( v2_tops_1 @ B @ A ) <=>
% 0.52/0.71             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.52/0.71  thf('28', plain,
% 0.52/0.71      (![X39 : $i, X40 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.52/0.71          | ((k1_tops_1 @ X40 @ X39) != (k1_xboole_0))
% 0.52/0.71          | (v2_tops_1 @ X39 @ X40)
% 0.52/0.71          | ~ (l1_pre_topc @ X40))),
% 0.52/0.71      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | (v2_tops_1 @ sk_B @ sk_A)
% 0.52/0.71        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.71  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('31', plain,
% 0.52/0.71      (((v2_tops_1 @ sk_B @ sk_A)
% 0.52/0.71        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.52/0.71         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['26', '31'])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (((v2_tops_1 @ sk_B @ sk_A))
% 0.52/0.71         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('simplify', [status(thm)], ['32'])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.52/0.71      inference('split', [status(esa)], ['0'])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.52/0.71       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.71  thf('36', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['2', '35'])).
% 0.52/0.71  thf('37', plain, (~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['1', '36'])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(t48_pre_topc, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      (![X31 : $i, X32 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.52/0.71          | (r1_tarski @ X31 @ (k2_pre_topc @ X32 @ X31))
% 0.52/0.71          | ~ (l1_pre_topc @ X32))),
% 0.52/0.71      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.71  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('42', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['40', '41'])).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(l78_tops_1, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( l1_pre_topc @ A ) =>
% 0.52/0.71       ( ![B:$i]:
% 0.52/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.71           ( ( k2_tops_1 @ A @ B ) =
% 0.52/0.71             ( k7_subset_1 @
% 0.52/0.71               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.52/0.71               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X33 : $i, X34 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.52/0.71          | ((k2_tops_1 @ X34 @ X33)
% 0.52/0.71              = (k7_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.52/0.71                 (k2_pre_topc @ X34 @ X33) @ (k1_tops_1 @ X34 @ X33)))
% 0.52/0.71          | ~ (l1_pre_topc @ X34))),
% 0.52/0.71      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.52/0.71  thf('45', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.52/0.71               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.52/0.71  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('47', plain,
% 0.52/0.71      (((k2_tops_1 @ sk_A @ sk_B)
% 0.52/0.71         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.52/0.71            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('demod', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.52/0.71      inference('split', [status(esa)], ['8'])).
% 0.52/0.71  thf('49', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('50', plain,
% 0.52/0.71      (![X39 : $i, X40 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.52/0.71          | ~ (v2_tops_1 @ X39 @ X40)
% 0.52/0.71          | ((k1_tops_1 @ X40 @ X39) = (k1_xboole_0))
% 0.52/0.71          | ~ (l1_pre_topc @ X40))),
% 0.52/0.71      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.52/0.71  thf('51', plain,
% 0.52/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.52/0.71        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.52/0.71        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['49', '50'])).
% 0.52/0.71  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('53', plain,
% 0.52/0.71      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.52/0.71        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('demod', [status(thm)], ['51', '52'])).
% 0.52/0.71  thf('54', plain,
% 0.52/0.71      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.52/0.71         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['48', '53'])).
% 0.52/0.71  thf('55', plain,
% 0.52/0.71      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.52/0.71       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.52/0.71      inference('split', [status(esa)], ['8'])).
% 0.52/0.71  thf('56', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['2', '35', '55'])).
% 0.52/0.71  thf('57', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['54', '56'])).
% 0.52/0.71  thf('58', plain,
% 0.52/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(dt_k2_pre_topc, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( l1_pre_topc @ A ) & 
% 0.52/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.52/0.71       ( m1_subset_1 @
% 0.52/0.71         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.52/0.71  thf('59', plain,
% 0.52/0.71      (![X29 : $i, X30 : $i]:
% 0.52/0.71         (~ (l1_pre_topc @ X29)
% 0.52/0.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.52/0.71          | (m1_subset_1 @ (k2_pre_topc @ X29 @ X30) @ 
% 0.52/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 0.52/0.71      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.52/0.71  thf('60', plain,
% 0.52/0.71      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.52/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.52/0.71      inference('sup-', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.52/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.71      inference('demod', [status(thm)], ['60', '61'])).
% 0.52/0.71  thf(redefinition_k7_subset_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.71         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.52/0.71          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.52/0.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.52/0.71           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['62', '63'])).
% 0.52/0.71  thf(d10_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.71  thf('65', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.52/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.71  thf('66', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.52/0.71      inference('simplify', [status(thm)], ['65'])).
% 0.52/0.71  thf(t85_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.52/0.71         (~ (r1_tarski @ X16 @ X17)
% 0.52/0.71          | (r1_xboole_0 @ X16 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.52/0.71  thf('68', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['66', '67'])).
% 0.52/0.71  thf(t4_subset_1, axiom,
% 0.52/0.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.71  thf('69', plain,
% 0.52/0.71      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.52/0.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.71  thf(t3_subset, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.71  thf('70', plain,
% 0.52/0.71      (![X23 : $i, X24 : $i]:
% 0.52/0.71         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.71  thf('71', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['69', '70'])).
% 0.52/0.71  thf('72', plain,
% 0.52/0.71      (![X3 : $i, X4 : $i]:
% 0.52/0.71         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.71  thf('73', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['71', '72'])).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.52/0.71         ((r1_xboole_0 @ X9 @ X10)
% 0.52/0.71          | ~ (r1_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X12)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.71  thf('76', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['68', '75'])).
% 0.52/0.71  thf(t83_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      (![X13 : $i, X14 : $i]:
% 0.52/0.71         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.52/0.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.52/0.71  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['76', '77'])).
% 0.52/0.71  thf('79', plain, (((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['47', '57', '64', '78'])).
% 0.52/0.71  thf('80', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.52/0.71      inference('demod', [status(thm)], ['42', '79'])).
% 0.52/0.71  thf('81', plain, ($false), inference('demod', [status(thm)], ['37', '80'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
