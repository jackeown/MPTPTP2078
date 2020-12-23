%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WHxbRphtWO

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:54 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 299 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          : 1026 (3999 expanded)
%              Number of equality atoms :   62 ( 209 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_tops_1 @ X28 @ X27 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k2_pre_topc @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X32 @ X31 ) @ X31 )
      | ~ ( v4_pre_topc @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k4_subset_1 @ X15 @ X14 @ X16 )
        = ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('29',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('47',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('57',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k2_tops_1 @ X30 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('63',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X25 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('64',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['61','67'])).

thf('69',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['31'])).

thf('70',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('72',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['32','70','71'])).

thf('73',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['30','72'])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('75',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('77',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','75','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('80',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['32','70'])).

thf('82',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WHxbRphtWO
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 267 iterations in 0.129s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.58  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.58  thf(t77_tops_1, conjecture,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.58           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.58             ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.58               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i]:
% 0.36/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.58          ( ![B:$i]:
% 0.36/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.58              ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.58                ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.58                  ( k7_subset_1 @
% 0.36/0.58                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(l78_tops_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_pre_topc @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.58           ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.58             ( k7_subset_1 @
% 0.36/0.58               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.36/0.58               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X27 : $i, X28 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.36/0.58          | ((k2_tops_1 @ X28 @ X27)
% 0.36/0.58              = (k7_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.36/0.58                 (k2_pre_topc @ X28 @ X27) @ (k1_tops_1 @ X28 @ X27)))
% 0.36/0.58          | ~ (l1_pre_topc @ X28))),
% 0.36/0.58      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.58        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.58            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t3_subset, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X22 : $i, X23 : $i]:
% 0.36/0.58         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.58  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58             (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.58        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('split', [status(esa)], ['8'])).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t69_tops_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_pre_topc @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.58           ( ( v4_pre_topc @ B @ A ) =>
% 0.36/0.58             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (![X31 : $i, X32 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.36/0.58          | (r1_tarski @ (k2_tops_1 @ X32 @ X31) @ X31)
% 0.36/0.58          | ~ (v4_pre_topc @ X31 @ X32)
% 0.36/0.58          | ~ (l1_pre_topc @ X32))),
% 0.36/0.58      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.58        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.58        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.58  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.58        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['9', '14'])).
% 0.36/0.58  thf(t1_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.58       ( r1_tarski @ A @ C ) ))).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.58         (~ (r1_tarski @ X9 @ X10)
% 0.36/0.58          | ~ (r1_tarski @ X10 @ X11)
% 0.36/0.58          | (r1_tarski @ X9 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      ((![X0 : $i]:
% 0.36/0.58          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.36/0.58           | ~ (r1_tarski @ sk_B @ X0)))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['7', '17'])).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (![X22 : $i, X24 : $i]:
% 0.36/0.58         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 0.36/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.58  thf('21', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.36/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15))
% 0.36/0.58          | ((k4_subset_1 @ X15 @ X14 @ X16) = (k2_xboole_0 @ X14 @ X16)))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.58            = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.58          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['20', '23'])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['9', '14'])).
% 0.36/0.58  thf(t12_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X7 : $i, X8 : $i]:
% 0.36/0.58         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.36/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.58  thf(commutativity_k2_xboole_0, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.58          = (sk_B)))
% 0.36/0.58         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('demod', [status(thm)], ['24', '29'])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58              (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.58        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      (~
% 0.36/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.58       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.58      inference('split', [status(esa)], ['31'])).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.58       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.36/0.58          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58             (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('split', [status(esa)], ['8'])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.36/0.58  thf('38', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf(t36_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.36/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.58  thf('40', plain,
% 0.36/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.58         (~ (r1_tarski @ X9 @ X10)
% 0.36/0.58          | ~ (r1_tarski @ X10 @ X11)
% 0.36/0.58          | (r1_tarski @ X9 @ X11))),
% 0.36/0.58      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.58  thf('42', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['38', '41'])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      (![X22 : $i, X24 : $i]:
% 0.36/0.58         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 0.36/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.36/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['37', '44'])).
% 0.36/0.58  thf('46', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.58            = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.58  thf('47', plain,
% 0.36/0.58      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.58          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.36/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      (![X7 : $i, X8 : $i]:
% 0.36/0.58         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.36/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.58  thf('52', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.36/0.58  thf('53', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.36/0.58      inference('demod', [status(thm)], ['51', '52'])).
% 0.36/0.58  thf('54', plain,
% 0.36/0.58      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['48', '53'])).
% 0.36/0.58  thf('55', plain,
% 0.36/0.58      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.58          = (sk_B)))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('demod', [status(thm)], ['47', '54'])).
% 0.36/0.58  thf('56', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t65_tops_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_pre_topc @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.58           ( ( k2_pre_topc @ A @ B ) =
% 0.36/0.58             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.58  thf('57', plain,
% 0.36/0.58      (![X29 : $i, X30 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.36/0.58          | ((k2_pre_topc @ X30 @ X29)
% 0.36/0.58              = (k4_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 0.36/0.58                 (k2_tops_1 @ X30 @ X29)))
% 0.36/0.58          | ~ (l1_pre_topc @ X30))),
% 0.36/0.58      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.36/0.58  thf('58', plain,
% 0.36/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.58        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.58            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('60', plain,
% 0.36/0.58      (((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.58         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.58  thf('61', plain,
% 0.36/0.58      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['55', '60'])).
% 0.36/0.58  thf('62', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(fc1_tops_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.36/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.58       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.36/0.58  thf('63', plain,
% 0.36/0.58      (![X25 : $i, X26 : $i]:
% 0.36/0.58         (~ (l1_pre_topc @ X25)
% 0.36/0.58          | ~ (v2_pre_topc @ X25)
% 0.36/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.36/0.58          | (v4_pre_topc @ (k2_pre_topc @ X25 @ X26) @ X25))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.36/0.58  thf('64', plain,
% 0.36/0.58      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.36/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.36/0.58  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('67', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.36/0.58      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.36/0.58  thf('68', plain,
% 0.36/0.58      (((v4_pre_topc @ sk_B @ sk_A))
% 0.36/0.58         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('sup+', [status(thm)], ['61', '67'])).
% 0.36/0.58  thf('69', plain,
% 0.36/0.58      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.58      inference('split', [status(esa)], ['31'])).
% 0.36/0.58  thf('70', plain,
% 0.36/0.58      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.58       ~
% 0.36/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.36/0.58  thf('71', plain,
% 0.36/0.58      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('split', [status(esa)], ['8'])).
% 0.36/0.58  thf('72', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['32', '70', '71'])).
% 0.36/0.58  thf('73', plain,
% 0.36/0.58      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.58         = (sk_B))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['30', '72'])).
% 0.36/0.58  thf('74', plain,
% 0.36/0.58      (((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.58         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.36/0.58  thf('75', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['73', '74'])).
% 0.36/0.58  thf('76', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.58  thf('77', plain,
% 0.36/0.58      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['4', '75', '76'])).
% 0.36/0.58  thf('78', plain,
% 0.36/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58              (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('split', [status(esa)], ['31'])).
% 0.36/0.58  thf('79', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.58           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.58  thf('80', plain,
% 0.36/0.58      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.58      inference('demod', [status(thm)], ['78', '79'])).
% 0.36/0.58  thf('81', plain,
% 0.36/0.58      (~
% 0.36/0.58       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.58             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['32', '70'])).
% 0.36/0.58  thf('82', plain,
% 0.36/0.58      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.58         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.36/0.58  thf('83', plain, ($false),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['77', '82'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
