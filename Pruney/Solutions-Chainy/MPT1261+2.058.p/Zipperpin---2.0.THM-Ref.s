%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AgmnU5D12g

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:46 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 332 expanded)
%              Number of leaves         :   33 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          : 1130 (4255 expanded)
%              Number of equality atoms :   67 ( 227 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 @ ( k2_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
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
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X51 @ X50 ) @ X50 )
      | ~ ( v4_pre_topc @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
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
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k2_xboole_0 @ X31 @ X33 ) ) ) ),
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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['4','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_tops_1 @ X45 @ X44 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k2_pre_topc @ X45 @ X44 ) @ ( k1_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X34 @ X36 )
        = ( k4_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('49',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('51',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('53',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('54',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('59',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('62',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('68',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('70',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('71',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','75'])).

thf('77',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['51','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('79',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X42 @ X43 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('80',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','83'])).

thf('85',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('86',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['50','86'])).

thf('88',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['49','87'])).

thf('89',plain,
    ( $false
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['45','88'])).

thf('90',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('91',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['50','86','90'])).

thf('92',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['89','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AgmnU5D12g
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.21  % Solved by: fo/fo7.sh
% 0.99/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.21  % done 2767 iterations in 0.771s
% 0.99/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.21  % SZS output start Refutation
% 0.99/1.21  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.99/1.21  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.99/1.21  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.21  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.99/1.21  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.21  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.99/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.21  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.99/1.21  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.99/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.21  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.21  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.21  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.21  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.99/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.21  thf(t77_tops_1, conjecture,
% 0.99/1.21    (![A:$i]:
% 0.99/1.21     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.21       ( ![B:$i]:
% 0.99/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.21           ( ( v4_pre_topc @ B @ A ) <=>
% 0.99/1.21             ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.21               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.99/1.21  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.21    (~( ![A:$i]:
% 0.99/1.21        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.21          ( ![B:$i]:
% 0.99/1.21            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.21              ( ( v4_pre_topc @ B @ A ) <=>
% 0.99/1.21                ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.21                  ( k7_subset_1 @
% 0.99/1.21                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.99/1.21    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.99/1.21  thf('0', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(t65_tops_1, axiom,
% 0.99/1.21    (![A:$i]:
% 0.99/1.21     ( ( l1_pre_topc @ A ) =>
% 0.99/1.21       ( ![B:$i]:
% 0.99/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.21           ( ( k2_pre_topc @ A @ B ) =
% 0.99/1.21             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.21  thf('1', plain,
% 0.99/1.21      (![X48 : $i, X49 : $i]:
% 0.99/1.21         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.99/1.21          | ((k2_pre_topc @ X49 @ X48)
% 0.99/1.21              = (k4_subset_1 @ (u1_struct_0 @ X49) @ X48 @ 
% 0.99/1.21                 (k2_tops_1 @ X49 @ X48)))
% 0.99/1.21          | ~ (l1_pre_topc @ X49))),
% 0.99/1.21      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.99/1.21  thf('2', plain,
% 0.99/1.21      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.21        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.21            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.21      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.21  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('4', plain,
% 0.99/1.21      (((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.21         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.21      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.21  thf('5', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(t3_subset, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.21  thf('6', plain,
% 0.99/1.21      (![X39 : $i, X40 : $i]:
% 0.99/1.21         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.21  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.99/1.21      inference('sup-', [status(thm)], ['5', '6'])).
% 0.99/1.21  thf('8', plain,
% 0.99/1.21      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21             (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.21        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('9', plain,
% 0.99/1.21      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('split', [status(esa)], ['8'])).
% 0.99/1.21  thf('10', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(t69_tops_1, axiom,
% 0.99/1.21    (![A:$i]:
% 0.99/1.21     ( ( l1_pre_topc @ A ) =>
% 0.99/1.21       ( ![B:$i]:
% 0.99/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.21           ( ( v4_pre_topc @ B @ A ) =>
% 0.99/1.21             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.99/1.21  thf('11', plain,
% 0.99/1.21      (![X50 : $i, X51 : $i]:
% 0.99/1.21         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.99/1.21          | (r1_tarski @ (k2_tops_1 @ X51 @ X50) @ X50)
% 0.99/1.21          | ~ (v4_pre_topc @ X50 @ X51)
% 0.99/1.21          | ~ (l1_pre_topc @ X51))),
% 0.99/1.21      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.99/1.21  thf('12', plain,
% 0.99/1.21      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.21        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.99/1.21        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.21      inference('sup-', [status(thm)], ['10', '11'])).
% 0.99/1.21  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('14', plain,
% 0.99/1.21      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.99/1.21        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.21      inference('demod', [status(thm)], ['12', '13'])).
% 0.99/1.21  thf('15', plain,
% 0.99/1.21      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['9', '14'])).
% 0.99/1.21  thf(t1_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.99/1.21       ( r1_tarski @ A @ C ) ))).
% 0.99/1.21  thf('16', plain,
% 0.99/1.21      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.99/1.21         (~ (r1_tarski @ X4 @ X5)
% 0.99/1.21          | ~ (r1_tarski @ X5 @ X6)
% 0.99/1.21          | (r1_tarski @ X4 @ X6))),
% 0.99/1.21      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.99/1.21  thf('17', plain,
% 0.99/1.21      ((![X0 : $i]:
% 0.99/1.21          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.99/1.21           | ~ (r1_tarski @ sk_B @ X0)))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['15', '16'])).
% 0.99/1.21  thf('18', plain,
% 0.99/1.21      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['7', '17'])).
% 0.99/1.21  thf('19', plain,
% 0.99/1.21      (![X39 : $i, X41 : $i]:
% 0.99/1.21         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.21  thf('20', plain,
% 0.99/1.21      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.21  thf('21', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(redefinition_k4_subset_1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.99/1.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.99/1.21       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.99/1.21  thf('22', plain,
% 0.99/1.21      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.99/1.21         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.99/1.21          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 0.99/1.21          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k2_xboole_0 @ X31 @ X33)))),
% 0.99/1.21      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.99/1.21  thf('23', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.21            = (k2_xboole_0 @ sk_B @ X0))
% 0.99/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.21      inference('sup-', [status(thm)], ['21', '22'])).
% 0.99/1.21  thf('24', plain,
% 0.99/1.21      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.21          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['20', '23'])).
% 0.99/1.21  thf(commutativity_k2_tarski, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.99/1.21  thf('25', plain,
% 0.99/1.21      (![X21 : $i, X22 : $i]:
% 0.99/1.21         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.99/1.21  thf(l51_zfmisc_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.21  thf('26', plain,
% 0.99/1.21      (![X23 : $i, X24 : $i]:
% 0.99/1.21         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.99/1.21      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.99/1.21  thf('27', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('sup+', [status(thm)], ['25', '26'])).
% 0.99/1.21  thf('28', plain,
% 0.99/1.21      (![X23 : $i, X24 : $i]:
% 0.99/1.21         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.99/1.21      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.99/1.21  thf('29', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('sup+', [status(thm)], ['27', '28'])).
% 0.99/1.21  thf('30', plain,
% 0.99/1.21      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['9', '14'])).
% 0.99/1.21  thf(t12_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.99/1.21  thf('31', plain,
% 0.99/1.21      (![X2 : $i, X3 : $i]:
% 0.99/1.21         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.99/1.21      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.99/1.21  thf('32', plain,
% 0.99/1.21      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['30', '31'])).
% 0.99/1.21  thf('33', plain,
% 0.99/1.21      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['29', '32'])).
% 0.99/1.21  thf('34', plain,
% 0.99/1.21      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.21          = (sk_B)))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['24', '33'])).
% 0.99/1.21  thf('35', plain,
% 0.99/1.21      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['4', '34'])).
% 0.99/1.21  thf('36', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(l78_tops_1, axiom,
% 0.99/1.21    (![A:$i]:
% 0.99/1.21     ( ( l1_pre_topc @ A ) =>
% 0.99/1.21       ( ![B:$i]:
% 0.99/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.21           ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.21             ( k7_subset_1 @
% 0.99/1.21               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.99/1.21               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.21  thf('37', plain,
% 0.99/1.21      (![X44 : $i, X45 : $i]:
% 0.99/1.21         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.99/1.21          | ((k2_tops_1 @ X45 @ X44)
% 0.99/1.21              = (k7_subset_1 @ (u1_struct_0 @ X45) @ 
% 0.99/1.21                 (k2_pre_topc @ X45 @ X44) @ (k1_tops_1 @ X45 @ X44)))
% 0.99/1.21          | ~ (l1_pre_topc @ X45))),
% 0.99/1.21      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.99/1.21  thf('38', plain,
% 0.99/1.21      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.21        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.21               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.21      inference('sup-', [status(thm)], ['36', '37'])).
% 0.99/1.21  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('40', plain,
% 0.99/1.21      (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.21            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.21      inference('demod', [status(thm)], ['38', '39'])).
% 0.99/1.21  thf('41', plain,
% 0.99/1.21      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21             (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('sup+', [status(thm)], ['35', '40'])).
% 0.99/1.21  thf('42', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(redefinition_k7_subset_1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.21       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.99/1.21  thf('43', plain,
% 0.99/1.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.99/1.21         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.99/1.21          | ((k7_subset_1 @ X35 @ X34 @ X36) = (k4_xboole_0 @ X34 @ X36)))),
% 0.99/1.21      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.99/1.21  thf('44', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.21           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['42', '43'])).
% 0.99/1.21  thf('45', plain,
% 0.99/1.21      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.21         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['41', '44'])).
% 0.99/1.21  thf('46', plain,
% 0.99/1.21      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21              (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.21        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('47', plain,
% 0.99/1.21      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21              (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.21         <= (~
% 0.99/1.21             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.21      inference('split', [status(esa)], ['46'])).
% 0.99/1.21  thf('48', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.21           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['42', '43'])).
% 0.99/1.21  thf('49', plain,
% 0.99/1.21      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.21         <= (~
% 0.99/1.21             (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.21      inference('demod', [status(thm)], ['47', '48'])).
% 0.99/1.21  thf('50', plain,
% 0.99/1.21      (~
% 0.99/1.21       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.99/1.21       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.21      inference('split', [status(esa)], ['46'])).
% 0.99/1.21  thf('51', plain,
% 0.99/1.21      (((k2_pre_topc @ sk_A @ sk_B)
% 0.99/1.21         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.21      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.21  thf('52', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.21           = (k4_xboole_0 @ sk_B @ X0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['42', '43'])).
% 0.99/1.21  thf('53', plain,
% 0.99/1.21      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21             (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.21         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.21      inference('split', [status(esa)], ['8'])).
% 0.99/1.21  thf('54', plain,
% 0.99/1.21      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.21         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.21                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.21                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.21      inference('sup+', [status(thm)], ['52', '53'])).
% 0.99/1.21  thf(t36_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.99/1.21  thf('55', plain,
% 0.99/1.21      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.99/1.21      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.21  thf(t44_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.99/1.21       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.99/1.21  thf('56', plain,
% 0.99/1.21      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.99/1.21         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.99/1.21          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 0.99/1.21      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.99/1.21  thf('57', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['55', '56'])).
% 0.99/1.21  thf('58', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.99/1.21      inference('sup-', [status(thm)], ['5', '6'])).
% 0.99/1.21  thf('59', plain,
% 0.99/1.21      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.99/1.21         (~ (r1_tarski @ X4 @ X5)
% 0.99/1.21          | ~ (r1_tarski @ X5 @ X6)
% 0.99/1.21          | (r1_tarski @ X4 @ X6))),
% 0.99/1.21      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.99/1.21  thf('60', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['58', '59'])).
% 0.99/1.21  thf('61', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['57', '60'])).
% 0.99/1.22  thf(t43_xboole_1, axiom,
% 0.99/1.22    (![A:$i,B:$i,C:$i]:
% 0.99/1.22     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.99/1.22       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.99/1.22  thf('62', plain,
% 0.99/1.22      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.22         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 0.99/1.22          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 0.99/1.22      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.99/1.22  thf('63', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.99/1.22      inference('sup-', [status(thm)], ['61', '62'])).
% 0.99/1.22  thf('64', plain,
% 0.99/1.22      (![X39 : $i, X41 : $i]:
% 0.99/1.22         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 0.99/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.22  thf('65', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.99/1.22          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.22      inference('sup-', [status(thm)], ['63', '64'])).
% 0.99/1.22  thf('66', plain,
% 0.99/1.22      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.22         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.99/1.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.22      inference('sup+', [status(thm)], ['54', '65'])).
% 0.99/1.22  thf('67', plain,
% 0.99/1.22      (![X0 : $i]:
% 0.99/1.22         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.99/1.22            = (k2_xboole_0 @ sk_B @ X0))
% 0.99/1.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['21', '22'])).
% 0.99/1.22  thf('68', plain,
% 0.99/1.22      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.22          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.99/1.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['66', '67'])).
% 0.99/1.22  thf('69', plain,
% 0.99/1.22      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.22      inference('sup+', [status(thm)], ['52', '53'])).
% 0.99/1.22  thf('70', plain,
% 0.99/1.22      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.99/1.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.99/1.22  thf('71', plain,
% 0.99/1.22      (![X2 : $i, X3 : $i]:
% 0.99/1.22         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.99/1.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.99/1.22  thf('72', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.99/1.22      inference('sup-', [status(thm)], ['70', '71'])).
% 0.99/1.22  thf('73', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.22      inference('sup+', [status(thm)], ['27', '28'])).
% 0.99/1.22  thf('74', plain,
% 0.99/1.22      (![X0 : $i, X1 : $i]:
% 0.99/1.22         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.99/1.22      inference('demod', [status(thm)], ['72', '73'])).
% 0.99/1.22  thf('75', plain,
% 0.99/1.22      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.99/1.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.22      inference('sup+', [status(thm)], ['69', '74'])).
% 0.99/1.22  thf('76', plain,
% 0.99/1.22      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.99/1.22          = (sk_B)))
% 0.99/1.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.22      inference('demod', [status(thm)], ['68', '75'])).
% 0.99/1.22  thf('77', plain,
% 0.99/1.22      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.99/1.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.22      inference('sup+', [status(thm)], ['51', '76'])).
% 0.99/1.22  thf('78', plain,
% 0.99/1.22      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf(fc1_tops_1, axiom,
% 0.99/1.22    (![A:$i,B:$i]:
% 0.99/1.22     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.99/1.22         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.22       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.99/1.22  thf('79', plain,
% 0.99/1.22      (![X42 : $i, X43 : $i]:
% 0.99/1.22         (~ (l1_pre_topc @ X42)
% 0.99/1.22          | ~ (v2_pre_topc @ X42)
% 0.99/1.22          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.99/1.22          | (v4_pre_topc @ (k2_pre_topc @ X42 @ X43) @ X42))),
% 0.99/1.22      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.99/1.22  thf('80', plain,
% 0.99/1.22      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.99/1.22        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.22        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.22      inference('sup-', [status(thm)], ['78', '79'])).
% 0.99/1.22  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.22  thf('83', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.99/1.22      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.99/1.22  thf('84', plain,
% 0.99/1.22      (((v4_pre_topc @ sk_B @ sk_A))
% 0.99/1.22         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.22      inference('sup+', [status(thm)], ['77', '83'])).
% 0.99/1.22  thf('85', plain,
% 0.99/1.22      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.22      inference('split', [status(esa)], ['46'])).
% 0.99/1.22  thf('86', plain,
% 0.99/1.22      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.99/1.22       ~
% 0.99/1.22       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sup-', [status(thm)], ['84', '85'])).
% 0.99/1.22  thf('87', plain,
% 0.99/1.22      (~
% 0.99/1.22       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('sat_resolution*', [status(thm)], ['50', '86'])).
% 0.99/1.22  thf('88', plain,
% 0.99/1.22      (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.22      inference('simpl_trail', [status(thm)], ['49', '87'])).
% 0.99/1.22  thf('89', plain, (($false) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.99/1.22      inference('simplify_reflect-', [status(thm)], ['45', '88'])).
% 0.99/1.22  thf('90', plain,
% 0.99/1.22      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.99/1.22       (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.22          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.99/1.22             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.22      inference('split', [status(esa)], ['8'])).
% 0.99/1.22  thf('91', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.99/1.22      inference('sat_resolution*', [status(thm)], ['50', '86', '90'])).
% 0.99/1.22  thf('92', plain, ($false),
% 0.99/1.22      inference('simpl_trail', [status(thm)], ['89', '91'])).
% 0.99/1.22  
% 0.99/1.22  % SZS output end Refutation
% 0.99/1.22  
% 0.99/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
