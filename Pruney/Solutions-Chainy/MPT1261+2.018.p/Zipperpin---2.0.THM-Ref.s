%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3MyU6SJPVO

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:39 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 347 expanded)
%              Number of leaves         :   37 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          : 1132 (4016 expanded)
%              Number of equality atoms :   97 ( 298 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_tops_1 @ X32 @ X31 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k2_pre_topc @ X32 @ X31 ) @ ( k1_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ( ( k2_pre_topc @ X30 @ X29 )
        = X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X17 @ X16 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X19 @ X18 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k4_subset_1 @ X22 @ X21 @ X23 )
        = ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('54',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('58',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('61',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_pre_topc @ X34 @ X33 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_pre_topc @ X30 )
      | ( ( k2_pre_topc @ X30 @ X29 )
       != X29 )
      | ( v4_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ( ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
       != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ X0 ) )
         != sk_B )
        | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','72'])).

thf('74',plain,
    ( ( ( ( k5_xboole_0 @ sk_B @ k1_xboole_0 )
       != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('76',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('79',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['5'])).

thf('81',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['14','79','80'])).

thf('82',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['12','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('84',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','82','83'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('87',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['14','79'])).

thf('89',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3MyU6SJPVO
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:48 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 307 iterations in 0.110s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.55  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.38/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.38/0.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.38/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.55  thf(t77_tops_1, conjecture,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.55             ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.55               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i]:
% 0.38/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.55          ( ![B:$i]:
% 0.38/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55              ( ( v4_pre_topc @ B @ A ) <=>
% 0.38/0.55                ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.55                  ( k7_subset_1 @
% 0.38/0.55                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(l78_tops_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( k2_tops_1 @ A @ B ) =
% 0.38/0.55             ( k7_subset_1 @
% 0.38/0.55               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.38/0.55               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (![X31 : $i, X32 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.38/0.55          | ((k2_tops_1 @ X32 @ X31)
% 0.38/0.55              = (k7_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.38/0.55                 (k2_pre_topc @ X32 @ X31) @ (k1_tops_1 @ X32 @ X31)))
% 0.38/0.55          | ~ (l1_pre_topc @ X32))),
% 0.38/0.55      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.38/0.55  thf('2', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.55               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.55  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.38/0.55            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t52_pre_topc, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.38/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.38/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      (![X29 : $i, X30 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.38/0.55          | ~ (v4_pre_topc @ X29 @ X30)
% 0.38/0.55          | ((k2_pre_topc @ X30 @ X29) = (X29))
% 0.38/0.55          | ~ (l1_pre_topc @ X30))),
% 0.38/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.38/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.55  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.38/0.55         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55              (k1_tops_1 @ sk_A @ sk_B)))
% 0.38/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      (~
% 0.38/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.38/0.55       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('split', [status(esa)], ['13'])).
% 0.38/0.55  thf(commutativity_k2_tarski, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         ((k2_tarski @ X17 @ X16) = (k2_tarski @ X16 @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.38/0.55  thf(t12_setfam_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (![X27 : $i, X28 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('17', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X27 : $i, X28 : $i]:
% 0.38/0.55         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 0.38/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.38/0.55  thf(t100_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.55  thf('20', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X6 @ X7)
% 0.38/0.55           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.55  thf(t3_boole, axiom,
% 0.38/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.55  thf('21', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.38/0.55      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 0.38/0.55      inference('sup+', [status(thm)], ['19', '22'])).
% 0.38/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.55  thf('24', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.38/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.55  thf(t28_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.38/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.55  thf('26', plain,
% 0.38/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['23', '26'])).
% 0.38/0.55  thf('28', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.38/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.55  thf(t36_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.38/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.55  thf('30', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.55      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.55  thf(l32_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X3 : $i, X5 : $i]:
% 0.38/0.55         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.55  thf('32', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X6 @ X7)
% 0.38/0.55           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.55  thf('34', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.55  thf('35', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.38/0.55      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (![X8 : $i, X9 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.38/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.55  thf('37', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.55  thf('38', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['34', '37'])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(dt_k7_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.38/0.55          | (m1_subset_1 @ (k7_subset_1 @ X19 @ X18 @ X20) @ 
% 0.38/0.55             (k1_zfmisc_1 @ X19)))),
% 0.38/0.55      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.38/0.55  thf('42', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.38/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.38/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['39', '42'])).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(redefinition_k4_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.38/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.55       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('45', plain,
% 0.38/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.38/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22))
% 0.38/0.55          | ((k4_subset_1 @ X22 @ X21 @ X23) = (k2_xboole_0 @ X21 @ X23)))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.38/0.55  thf('46', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.55            = (k2_xboole_0 @ sk_B @ X0))
% 0.38/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.55          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['43', '46'])).
% 0.38/0.55  thf('48', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.38/0.55  thf('49', plain,
% 0.38/0.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.38/0.55          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 0.38/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.38/0.55  thf('50', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.55  thf('53', plain,
% 0.38/0.55      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.38/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.55  thf('54', plain,
% 0.38/0.55      (![X3 : $i, X5 : $i]:
% 0.38/0.55         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.38/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['52', '55'])).
% 0.38/0.55  thf(t98_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.55  thf('57', plain,
% 0.38/0.55      (![X14 : $i, X15 : $i]:
% 0.38/0.55         ((k2_xboole_0 @ X14 @ X15)
% 0.38/0.55           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.55          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['56', '57'])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.38/0.55          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('demod', [status(thm)], ['47', '58'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(t65_tops_1, axiom,
% 0.38/0.55    (![A:$i]:
% 0.38/0.55     ( ( l1_pre_topc @ A ) =>
% 0.38/0.55       ( ![B:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.55           ( ( k2_pre_topc @ A @ B ) =
% 0.38/0.55             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.55  thf('61', plain,
% 0.38/0.55      (![X33 : $i, X34 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.38/0.55          | ((k2_pre_topc @ X34 @ X33)
% 0.38/0.55              = (k4_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.38/0.55                 (k2_tops_1 @ X34 @ X33)))
% 0.38/0.55          | ~ (l1_pre_topc @ X34))),
% 0.38/0.55      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.55            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.55  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('64', plain,
% 0.38/0.55      (((k2_pre_topc @ sk_A @ sk_B)
% 0.38/0.55         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['62', '63'])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      ((((k2_pre_topc @ sk_A @ sk_B) = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['59', '64'])).
% 0.38/0.55  thf('66', plain,
% 0.38/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('67', plain,
% 0.38/0.55      (![X29 : $i, X30 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.38/0.55          | ~ (v2_pre_topc @ X30)
% 0.38/0.55          | ((k2_pre_topc @ X30 @ X29) != (X29))
% 0.38/0.55          | (v4_pre_topc @ X29 @ X30)
% 0.38/0.55          | ~ (l1_pre_topc @ X30))),
% 0.38/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.38/0.55  thf('68', plain,
% 0.38/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.55        | (v4_pre_topc @ sk_B @ sk_A)
% 0.38/0.55        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 0.38/0.55        | ~ (v2_pre_topc @ sk_A))),
% 0.38/0.55      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.55  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('71', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.38/0.55  thf('72', plain,
% 0.38/0.55      (((((k5_xboole_0 @ sk_B @ k1_xboole_0) != (sk_B))
% 0.38/0.55         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['65', '71'])).
% 0.38/0.55  thf('73', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (((k5_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ X0)) != (sk_B))
% 0.38/0.55           | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['38', '72'])).
% 0.38/0.55  thf('74', plain,
% 0.38/0.55      (((((k5_xboole_0 @ sk_B @ k1_xboole_0) != (sk_B))
% 0.38/0.55         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['27', '73'])).
% 0.38/0.55  thf('75', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.55      inference('demod', [status(thm)], ['23', '26'])).
% 0.38/0.55  thf('76', plain,
% 0.38/0.55      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('demod', [status(thm)], ['74', '75'])).
% 0.38/0.55  thf('77', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A))
% 0.38/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('simplify', [status(thm)], ['76'])).
% 0.38/0.55  thf('78', plain,
% 0.38/0.55      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.55      inference('split', [status(esa)], ['13'])).
% 0.38/0.55  thf('79', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.38/0.55       ~
% 0.38/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['77', '78'])).
% 0.38/0.55  thf('80', plain,
% 0.38/0.55      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.38/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('81', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['14', '79', '80'])).
% 0.38/0.55  thf('82', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['12', '81'])).
% 0.38/0.55  thf('83', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.55  thf('84', plain,
% 0.38/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('demod', [status(thm)], ['4', '82', '83'])).
% 0.38/0.55  thf('85', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55              (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= (~
% 0.38/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('split', [status(esa)], ['13'])).
% 0.38/0.55  thf('86', plain,
% 0.38/0.55      (![X0 : $i]:
% 0.38/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.38/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.38/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.55  thf('87', plain,
% 0.38/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.38/0.55         <= (~
% 0.38/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.38/0.55      inference('demod', [status(thm)], ['85', '86'])).
% 0.38/0.55  thf('88', plain,
% 0.38/0.55      (~
% 0.38/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.38/0.55             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['14', '79'])).
% 0.38/0.55  thf('89', plain,
% 0.38/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.38/0.55         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.38/0.55      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 0.38/0.55  thf('90', plain, ($false),
% 0.38/0.55      inference('simplify_reflect-', [status(thm)], ['84', '89'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
