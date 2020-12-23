%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2QaA0k9hF9

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:20 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 847 expanded)
%              Number of leaves         :   36 ( 267 expanded)
%              Depth                    :   15
%              Number of atoms          : 1249 (7347 expanded)
%              Number of equality atoms :   83 ( 515 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
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

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k1_tops_1 @ X44 @ X43 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X44 ) @ X43 @ ( k2_tops_1 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k1_tops_1 @ X38 @ ( k2_tops_1 @ X38 @ ( k2_tops_1 @ X38 @ X37 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['10','11','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ k1_xboole_0 ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_subset_1 @ X17 @ X18 )
        = ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X22 @ ( k3_subset_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('65',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('77',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('79',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','77','84'])).

thf('86',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('91',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('92',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X42 @ X41 ) @ X41 )
      | ~ ( v4_pre_topc @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('97',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X33 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('98',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ sk_A )
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
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l79_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) )
            = ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('103',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ ( k2_tops_1 @ X36 @ X35 ) )
        = ( k2_tops_1 @ X36 @ X35 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[l79_tops_1])).

thf('104',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['101','107'])).

thf('109',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','108'])).

thf('110',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('112',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','90','109','110','111'])).

thf('113',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
 != ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2QaA0k9hF9
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.80/2.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.80/2.04  % Solved by: fo/fo7.sh
% 1.80/2.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.80/2.04  % done 3279 iterations in 1.590s
% 1.80/2.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.80/2.04  % SZS output start Refutation
% 1.80/2.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.80/2.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.80/2.04  thf(sk_B_type, type, sk_B: $i).
% 1.80/2.04  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.80/2.04  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.80/2.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.80/2.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.80/2.04  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.80/2.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.80/2.04  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.80/2.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.80/2.04  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.80/2.04  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.80/2.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.80/2.04  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.80/2.04  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.80/2.04  thf(sk_A_type, type, sk_A: $i).
% 1.80/2.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.80/2.04  thf(t75_tops_1, conjecture,
% 1.80/2.04    (![A:$i]:
% 1.80/2.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.80/2.04       ( ![B:$i]:
% 1.80/2.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/2.04           ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.80/2.04             ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.80/2.04  thf(zf_stmt_0, negated_conjecture,
% 1.80/2.04    (~( ![A:$i]:
% 1.80/2.04        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.80/2.04          ( ![B:$i]:
% 1.80/2.04            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/2.04              ( ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.80/2.04                ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 1.80/2.04    inference('cnf.neg', [status(esa)], [t75_tops_1])).
% 1.80/2.04  thf('0', plain,
% 1.80/2.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf(dt_k2_tops_1, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( ( l1_pre_topc @ A ) & 
% 1.80/2.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.80/2.04       ( m1_subset_1 @
% 1.80/2.04         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.80/2.04  thf('1', plain,
% 1.80/2.04      (![X31 : $i, X32 : $i]:
% 1.80/2.04         (~ (l1_pre_topc @ X31)
% 1.80/2.04          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.80/2.04          | (m1_subset_1 @ (k2_tops_1 @ X31 @ X32) @ 
% 1.80/2.04             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 1.80/2.04      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.80/2.04  thf('2', plain,
% 1.80/2.04      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.80/2.04         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.80/2.04        | ~ (l1_pre_topc @ sk_A))),
% 1.80/2.04      inference('sup-', [status(thm)], ['0', '1'])).
% 1.80/2.04  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('4', plain,
% 1.80/2.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.80/2.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/2.04      inference('demod', [status(thm)], ['2', '3'])).
% 1.80/2.04  thf('5', plain,
% 1.80/2.04      (![X31 : $i, X32 : $i]:
% 1.80/2.04         (~ (l1_pre_topc @ X31)
% 1.80/2.04          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.80/2.04          | (m1_subset_1 @ (k2_tops_1 @ X31 @ X32) @ 
% 1.80/2.04             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 1.80/2.04      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.80/2.04  thf('6', plain,
% 1.80/2.04      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.80/2.04        | ~ (l1_pre_topc @ sk_A))),
% 1.80/2.04      inference('sup-', [status(thm)], ['4', '5'])).
% 1.80/2.04  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('8', plain,
% 1.80/2.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/2.04      inference('demod', [status(thm)], ['6', '7'])).
% 1.80/2.04  thf(t74_tops_1, axiom,
% 1.80/2.04    (![A:$i]:
% 1.80/2.04     ( ( l1_pre_topc @ A ) =>
% 1.80/2.04       ( ![B:$i]:
% 1.80/2.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/2.04           ( ( k1_tops_1 @ A @ B ) =
% 1.80/2.04             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.80/2.04  thf('9', plain,
% 1.80/2.04      (![X43 : $i, X44 : $i]:
% 1.80/2.04         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 1.80/2.04          | ((k1_tops_1 @ X44 @ X43)
% 1.80/2.04              = (k7_subset_1 @ (u1_struct_0 @ X44) @ X43 @ 
% 1.80/2.04                 (k2_tops_1 @ X44 @ X43)))
% 1.80/2.04          | ~ (l1_pre_topc @ X44))),
% 1.80/2.04      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.80/2.04  thf('10', plain,
% 1.80/2.04      ((~ (l1_pre_topc @ sk_A)
% 1.80/2.04        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.80/2.04            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.80/2.04               (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04               (k2_tops_1 @ sk_A @ 
% 1.80/2.04                (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))))),
% 1.80/2.04      inference('sup-', [status(thm)], ['8', '9'])).
% 1.80/2.04  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('12', plain,
% 1.80/2.04      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf(l80_tops_1, axiom,
% 1.80/2.04    (![A:$i]:
% 1.80/2.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.80/2.04       ( ![B:$i]:
% 1.80/2.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/2.04           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 1.80/2.04             ( k1_xboole_0 ) ) ) ) ))).
% 1.80/2.04  thf('13', plain,
% 1.80/2.04      (![X37 : $i, X38 : $i]:
% 1.80/2.04         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.80/2.04          | ((k1_tops_1 @ X38 @ (k2_tops_1 @ X38 @ (k2_tops_1 @ X38 @ X37)))
% 1.80/2.04              = (k1_xboole_0))
% 1.80/2.04          | ~ (l1_pre_topc @ X38)
% 1.80/2.04          | ~ (v2_pre_topc @ X38))),
% 1.80/2.04      inference('cnf', [status(esa)], [l80_tops_1])).
% 1.80/2.04  thf('14', plain,
% 1.80/2.04      ((~ (v2_pre_topc @ sk_A)
% 1.80/2.04        | ~ (l1_pre_topc @ sk_A)
% 1.80/2.04        | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.80/2.04            = (k1_xboole_0)))),
% 1.80/2.04      inference('sup-', [status(thm)], ['12', '13'])).
% 1.80/2.04  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('17', plain,
% 1.80/2.04      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.80/2.04         = (k1_xboole_0))),
% 1.80/2.04      inference('demod', [status(thm)], ['14', '15', '16'])).
% 1.80/2.04  thf('18', plain,
% 1.80/2.04      (((k1_xboole_0)
% 1.80/2.04         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.80/2.04            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 1.80/2.04      inference('demod', [status(thm)], ['10', '11', '17'])).
% 1.80/2.04  thf('19', plain,
% 1.80/2.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/2.04      inference('demod', [status(thm)], ['6', '7'])).
% 1.80/2.04  thf(redefinition_k7_subset_1, axiom,
% 1.80/2.04    (![A:$i,B:$i,C:$i]:
% 1.80/2.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.04       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.80/2.04  thf('20', plain,
% 1.80/2.04      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.80/2.04         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.80/2.04          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 1.80/2.04      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.80/2.04  thf('21', plain,
% 1.80/2.04      (![X0 : $i]:
% 1.80/2.04         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.80/2.04           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0)
% 1.80/2.04           = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['19', '20'])).
% 1.80/2.04  thf('22', plain,
% 1.80/2.04      (((k1_xboole_0)
% 1.80/2.04         = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 1.80/2.04      inference('demod', [status(thm)], ['18', '21'])).
% 1.80/2.04  thf(d10_xboole_0, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.80/2.04  thf('23', plain,
% 1.80/2.04      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.80/2.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.80/2.04  thf('24', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.80/2.04      inference('simplify', [status(thm)], ['23'])).
% 1.80/2.04  thf(l32_xboole_1, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.80/2.04  thf('25', plain,
% 1.80/2.04      (![X5 : $i, X7 : $i]:
% 1.80/2.04         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.80/2.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.80/2.04  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['24', '25'])).
% 1.80/2.04  thf(t41_xboole_1, axiom,
% 1.80/2.04    (![A:$i,B:$i,C:$i]:
% 1.80/2.04     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.80/2.04       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.80/2.04  thf('27', plain,
% 1.80/2.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.80/2.04           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.80/2.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.80/2.04  thf('28', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         ((k1_xboole_0)
% 1.80/2.04           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.80/2.04      inference('sup+', [status(thm)], ['26', '27'])).
% 1.80/2.04  thf('29', plain,
% 1.80/2.04      (![X5 : $i, X6 : $i]:
% 1.80/2.04         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.80/2.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.80/2.04  thf('30', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         (((k1_xboole_0) != (k1_xboole_0))
% 1.80/2.04          | (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.80/2.04      inference('sup-', [status(thm)], ['28', '29'])).
% 1.80/2.04  thf('31', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.80/2.04      inference('simplify', [status(thm)], ['30'])).
% 1.80/2.04  thf('32', plain,
% 1.80/2.04      (![X2 : $i, X4 : $i]:
% 1.80/2.04         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.80/2.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.80/2.04  thf('33', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X1)
% 1.80/2.04          | ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X1)))),
% 1.80/2.04      inference('sup-', [status(thm)], ['31', '32'])).
% 1.80/2.04  thf('34', plain,
% 1.80/2.04      ((~ (r1_tarski @ 
% 1.80/2.04           (k2_xboole_0 @ 
% 1.80/2.04            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.80/2.04            k1_xboole_0) @ 
% 1.80/2.04           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.80/2.04        | ((k2_xboole_0 @ 
% 1.80/2.04            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.80/2.04            (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04             (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))
% 1.80/2.04            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.80/2.04      inference('sup-', [status(thm)], ['22', '33'])).
% 1.80/2.04  thf('35', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.80/2.04      inference('simplify', [status(thm)], ['23'])).
% 1.80/2.04  thf(t3_subset, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.80/2.04  thf('36', plain,
% 1.80/2.04      (![X26 : $i, X28 : $i]:
% 1.80/2.04         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 1.80/2.04      inference('cnf', [status(esa)], [t3_subset])).
% 1.80/2.04  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['35', '36'])).
% 1.80/2.04  thf(dt_k3_subset_1, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.04       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.80/2.04  thf('38', plain,
% 1.80/2.04      (![X19 : $i, X20 : $i]:
% 1.80/2.04         ((m1_subset_1 @ (k3_subset_1 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 1.80/2.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 1.80/2.04      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.80/2.04  thf('39', plain,
% 1.80/2.04      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['37', '38'])).
% 1.80/2.04  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['35', '36'])).
% 1.80/2.04  thf(d5_subset_1, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.04       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.80/2.04  thf('41', plain,
% 1.80/2.04      (![X17 : $i, X18 : $i]:
% 1.80/2.04         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 1.80/2.04          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 1.80/2.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.80/2.04  thf('42', plain,
% 1.80/2.04      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['40', '41'])).
% 1.80/2.04  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['24', '25'])).
% 1.80/2.04  thf('44', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup+', [status(thm)], ['42', '43'])).
% 1.80/2.04  thf('45', plain,
% 1.80/2.04      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.80/2.04      inference('demod', [status(thm)], ['39', '44'])).
% 1.80/2.04  thf('46', plain,
% 1.80/2.04      (![X17 : $i, X18 : $i]:
% 1.80/2.04         (((k3_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))
% 1.80/2.04          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 1.80/2.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.80/2.04  thf('47', plain,
% 1.80/2.04      (![X0 : $i]:
% 1.80/2.04         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['45', '46'])).
% 1.80/2.04  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['35', '36'])).
% 1.80/2.04  thf(involutiveness_k3_subset_1, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.80/2.04       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.80/2.04  thf('49', plain,
% 1.80/2.04      (![X21 : $i, X22 : $i]:
% 1.80/2.04         (((k3_subset_1 @ X22 @ (k3_subset_1 @ X22 @ X21)) = (X21))
% 1.80/2.04          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 1.80/2.04      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.80/2.04  thf('50', plain,
% 1.80/2.04      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['48', '49'])).
% 1.80/2.04  thf('51', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup+', [status(thm)], ['42', '43'])).
% 1.80/2.04  thf('52', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.80/2.04      inference('demod', [status(thm)], ['50', '51'])).
% 1.80/2.04  thf('53', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.80/2.04      inference('demod', [status(thm)], ['47', '52'])).
% 1.80/2.04  thf('54', plain,
% 1.80/2.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.80/2.04           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.80/2.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.80/2.04  thf('55', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X1 @ X0)
% 1.80/2.04           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.80/2.04      inference('sup+', [status(thm)], ['53', '54'])).
% 1.80/2.04  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['24', '25'])).
% 1.80/2.04  thf('57', plain,
% 1.80/2.04      (![X0 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup+', [status(thm)], ['55', '56'])).
% 1.80/2.04  thf(t48_xboole_1, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.80/2.04  thf('58', plain,
% 1.80/2.04      (![X15 : $i, X16 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.80/2.04           = (k3_xboole_0 @ X15 @ X16))),
% 1.80/2.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.80/2.04  thf('59', plain,
% 1.80/2.04      (![X0 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 1.80/2.04           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 1.80/2.04      inference('sup+', [status(thm)], ['57', '58'])).
% 1.80/2.04  thf('60', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.80/2.04      inference('demod', [status(thm)], ['47', '52'])).
% 1.80/2.04  thf(commutativity_k3_xboole_0, axiom,
% 1.80/2.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.80/2.04  thf('61', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.80/2.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.80/2.04  thf('62', plain,
% 1.80/2.04      (![X0 : $i]:
% 1.80/2.04         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 1.80/2.04           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.80/2.04      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.80/2.04  thf('63', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.80/2.04      inference('demod', [status(thm)], ['47', '52'])).
% 1.80/2.04  thf('64', plain,
% 1.80/2.04      (![X15 : $i, X16 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.80/2.04           = (k3_xboole_0 @ X15 @ X16))),
% 1.80/2.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.80/2.04  thf('65', plain,
% 1.80/2.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.80/2.04           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.80/2.04      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.80/2.04  thf('66', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.80/2.04           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 1.80/2.04      inference('sup+', [status(thm)], ['64', '65'])).
% 1.80/2.04  thf('67', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)
% 1.80/2.04           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.80/2.04      inference('sup+', [status(thm)], ['63', '66'])).
% 1.80/2.04  thf('68', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.80/2.04      inference('simplify', [status(thm)], ['23'])).
% 1.80/2.04  thf(t28_xboole_1, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.80/2.04  thf('69', plain,
% 1.80/2.04      (![X10 : $i, X11 : $i]:
% 1.80/2.04         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.80/2.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.80/2.04  thf('70', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['68', '69'])).
% 1.80/2.04  thf('71', plain,
% 1.80/2.04      (![X15 : $i, X16 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.80/2.04           = (k3_xboole_0 @ X15 @ X16))),
% 1.80/2.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.80/2.04  thf('72', plain,
% 1.80/2.04      (![X15 : $i, X16 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.80/2.04           = (k3_xboole_0 @ X15 @ X16))),
% 1.80/2.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.80/2.04  thf('73', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.80/2.04           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.80/2.04      inference('sup+', [status(thm)], ['71', '72'])).
% 1.80/2.04  thf('74', plain,
% 1.80/2.04      (![X0 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X0 @ X0)
% 1.80/2.04           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 1.80/2.04      inference('sup+', [status(thm)], ['70', '73'])).
% 1.80/2.04  thf('75', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['24', '25'])).
% 1.80/2.04  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['24', '25'])).
% 1.80/2.04  thf('77', plain,
% 1.80/2.04      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.80/2.04      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.80/2.04  thf('78', plain,
% 1.80/2.04      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['37', '38'])).
% 1.80/2.04  thf('79', plain,
% 1.80/2.04      (![X26 : $i, X27 : $i]:
% 1.80/2.04         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.80/2.04      inference('cnf', [status(esa)], [t3_subset])).
% 1.80/2.04  thf('80', plain, (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X0)),
% 1.80/2.04      inference('sup-', [status(thm)], ['78', '79'])).
% 1.80/2.04  thf('81', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup+', [status(thm)], ['42', '43'])).
% 1.80/2.04  thf('82', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.80/2.04      inference('demod', [status(thm)], ['80', '81'])).
% 1.80/2.04  thf('83', plain,
% 1.80/2.04      (![X5 : $i, X7 : $i]:
% 1.80/2.04         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.80/2.04      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.80/2.04  thf('84', plain,
% 1.80/2.04      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.80/2.04      inference('sup-', [status(thm)], ['82', '83'])).
% 1.80/2.04  thf('85', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.80/2.04      inference('demod', [status(thm)], ['67', '77', '84'])).
% 1.80/2.04  thf('86', plain,
% 1.80/2.04      (![X15 : $i, X16 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.80/2.04           = (k3_xboole_0 @ X15 @ X16))),
% 1.80/2.04      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.80/2.04  thf('87', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 1.80/2.04           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.80/2.04      inference('sup+', [status(thm)], ['85', '86'])).
% 1.80/2.04  thf('88', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.80/2.04      inference('demod', [status(thm)], ['47', '52'])).
% 1.80/2.04  thf('89', plain,
% 1.80/2.04      (![X0 : $i, X1 : $i]:
% 1.80/2.04         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.80/2.04      inference('demod', [status(thm)], ['87', '88'])).
% 1.80/2.04  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.80/2.04      inference('demod', [status(thm)], ['62', '89'])).
% 1.80/2.04  thf('91', plain,
% 1.80/2.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/2.04      inference('demod', [status(thm)], ['6', '7'])).
% 1.80/2.04  thf(t69_tops_1, axiom,
% 1.80/2.04    (![A:$i]:
% 1.80/2.04     ( ( l1_pre_topc @ A ) =>
% 1.80/2.04       ( ![B:$i]:
% 1.80/2.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/2.04           ( ( v4_pre_topc @ B @ A ) =>
% 1.80/2.04             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.80/2.04  thf('92', plain,
% 1.80/2.04      (![X41 : $i, X42 : $i]:
% 1.80/2.04         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 1.80/2.04          | (r1_tarski @ (k2_tops_1 @ X42 @ X41) @ X41)
% 1.80/2.04          | ~ (v4_pre_topc @ X41 @ X42)
% 1.80/2.04          | ~ (l1_pre_topc @ X42))),
% 1.80/2.04      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.80/2.04  thf('93', plain,
% 1.80/2.04      ((~ (l1_pre_topc @ sk_A)
% 1.80/2.04        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04             sk_A)
% 1.80/2.04        | (r1_tarski @ 
% 1.80/2.04           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.80/2.04           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.80/2.04      inference('sup-', [status(thm)], ['91', '92'])).
% 1.80/2.04  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('95', plain,
% 1.80/2.04      ((~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 1.80/2.04        | (r1_tarski @ 
% 1.80/2.04           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.80/2.04           (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.80/2.04      inference('demod', [status(thm)], ['93', '94'])).
% 1.80/2.04  thf('96', plain,
% 1.80/2.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/2.04      inference('demod', [status(thm)], ['6', '7'])).
% 1.80/2.04  thf(fc1_tops_1, axiom,
% 1.80/2.04    (![A:$i,B:$i]:
% 1.80/2.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.80/2.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.80/2.04       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.80/2.04  thf('97', plain,
% 1.80/2.04      (![X33 : $i, X34 : $i]:
% 1.80/2.04         (~ (l1_pre_topc @ X33)
% 1.80/2.04          | ~ (v2_pre_topc @ X33)
% 1.80/2.04          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.80/2.04          | (v4_pre_topc @ (k2_pre_topc @ X33 @ X34) @ X33))),
% 1.80/2.04      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.80/2.04  thf('98', plain,
% 1.80/2.04      (((v4_pre_topc @ 
% 1.80/2.04         (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.80/2.04         sk_A)
% 1.80/2.04        | ~ (v2_pre_topc @ sk_A)
% 1.80/2.04        | ~ (l1_pre_topc @ sk_A))),
% 1.80/2.04      inference('sup-', [status(thm)], ['96', '97'])).
% 1.80/2.04  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('101', plain,
% 1.80/2.04      ((v4_pre_topc @ 
% 1.80/2.04        (k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.80/2.04        sk_A)),
% 1.80/2.04      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.80/2.04  thf('102', plain,
% 1.80/2.04      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.80/2.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.80/2.04      inference('demod', [status(thm)], ['2', '3'])).
% 1.80/2.04  thf(l79_tops_1, axiom,
% 1.80/2.04    (![A:$i]:
% 1.80/2.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.80/2.04       ( ![B:$i]:
% 1.80/2.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.80/2.04           ( ( k2_pre_topc @ A @ ( k2_tops_1 @ A @ B ) ) =
% 1.80/2.04             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 1.80/2.04  thf('103', plain,
% 1.80/2.04      (![X35 : $i, X36 : $i]:
% 1.80/2.04         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.80/2.04          | ((k2_pre_topc @ X36 @ (k2_tops_1 @ X36 @ X35))
% 1.80/2.04              = (k2_tops_1 @ X36 @ X35))
% 1.80/2.04          | ~ (l1_pre_topc @ X36)
% 1.80/2.04          | ~ (v2_pre_topc @ X36))),
% 1.80/2.04      inference('cnf', [status(esa)], [l79_tops_1])).
% 1.80/2.04  thf('104', plain,
% 1.80/2.04      ((~ (v2_pre_topc @ sk_A)
% 1.80/2.04        | ~ (l1_pre_topc @ sk_A)
% 1.80/2.04        | ((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.80/2.04            = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.80/2.04      inference('sup-', [status(thm)], ['102', '103'])).
% 1.80/2.04  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('107', plain,
% 1.80/2.04      (((k2_pre_topc @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.80/2.04         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.80/2.04      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.80/2.04  thf('108', plain,
% 1.80/2.04      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 1.80/2.04      inference('demod', [status(thm)], ['101', '107'])).
% 1.80/2.04  thf('109', plain,
% 1.80/2.04      ((r1_tarski @ 
% 1.80/2.04        (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.80/2.04        (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.80/2.04      inference('demod', [status(thm)], ['95', '108'])).
% 1.80/2.04  thf('110', plain,
% 1.80/2.04      (((k1_xboole_0)
% 1.80/2.04         = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.80/2.04            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))))),
% 1.80/2.04      inference('demod', [status(thm)], ['18', '21'])).
% 1.80/2.04  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.80/2.04      inference('demod', [status(thm)], ['62', '89'])).
% 1.80/2.04  thf('112', plain,
% 1.80/2.04      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.80/2.04         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.80/2.04      inference('demod', [status(thm)], ['34', '90', '109', '110', '111'])).
% 1.80/2.04  thf('113', plain,
% 1.80/2.04      (((k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.80/2.04         != (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.80/2.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.80/2.04  thf('114', plain, ($false),
% 1.80/2.04      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 1.80/2.04  
% 1.80/2.04  % SZS output end Refutation
% 1.80/2.04  
% 1.80/2.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
