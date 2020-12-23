%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tXvxDiYcTx

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:12 EST 2020

% Result     : Theorem 9.23s
% Output     : Refutation 9.23s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 170 expanded)
%              Number of leaves         :   26 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  926 (2803 expanded)
%              Number of equality atoms :   35 (  47 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t67_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_tops_1 @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k2_tops_1 @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k4_subset_1 @ X11 @ X10 @ X12 )
        = ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('12',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t66_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_tops_1 @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X22 @ ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X23 ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_tops_1 @ X22 @ X21 ) @ ( k2_tops_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_tops_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k2_tops_1 @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X18 @ X16 )
        = ( k9_subset_1 @ X17 @ X18 @ ( k3_subset_1 @ X17 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_C )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k7_subset_1 @ X14 @ X13 @ X15 )
        = ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('46',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('47',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','37','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('50',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('51',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k2_tops_1 @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_tops_1 @ X20 @ X19 )
        = ( k2_tops_1 @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_C )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_tops_1 @ sk_A @ sk_C )
    = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','48','55','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['6','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tXvxDiYcTx
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:14:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 9.23/9.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.23/9.47  % Solved by: fo/fo7.sh
% 9.23/9.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.23/9.47  % done 1882 iterations in 9.018s
% 9.23/9.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.23/9.47  % SZS output start Refutation
% 9.23/9.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 9.23/9.47  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 9.23/9.47  thf(sk_C_type, type, sk_C: $i).
% 9.23/9.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.23/9.47  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 9.23/9.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 9.23/9.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.23/9.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.23/9.47  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 9.23/9.47  thf(sk_B_type, type, sk_B: $i).
% 9.23/9.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.23/9.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.23/9.47  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 9.23/9.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.23/9.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 9.23/9.47  thf(sk_A_type, type, sk_A: $i).
% 9.23/9.47  thf(t67_tops_1, conjecture,
% 9.23/9.47    (![A:$i]:
% 9.23/9.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.23/9.47       ( ![B:$i]:
% 9.23/9.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.23/9.47           ( ![C:$i]:
% 9.23/9.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.23/9.47               ( r1_tarski @
% 9.23/9.47                 ( k2_tops_1 @
% 9.23/9.47                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 9.23/9.47                 ( k4_subset_1 @
% 9.23/9.47                   ( u1_struct_0 @ A ) @ ( k2_tops_1 @ A @ B ) @ 
% 9.23/9.47                   ( k2_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 9.23/9.47  thf(zf_stmt_0, negated_conjecture,
% 9.23/9.47    (~( ![A:$i]:
% 9.23/9.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.23/9.47          ( ![B:$i]:
% 9.23/9.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.23/9.47              ( ![C:$i]:
% 9.23/9.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.23/9.47                  ( r1_tarski @
% 9.23/9.47                    ( k2_tops_1 @
% 9.23/9.47                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 9.23/9.47                    ( k4_subset_1 @
% 9.23/9.47                      ( u1_struct_0 @ A ) @ ( k2_tops_1 @ A @ B ) @ 
% 9.23/9.47                      ( k2_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 9.23/9.47    inference('cnf.neg', [status(esa)], [t67_tops_1])).
% 9.23/9.47  thf('0', plain,
% 9.23/9.47      (~ (r1_tarski @ 
% 9.23/9.47          (k2_tops_1 @ sk_A @ 
% 9.23/9.47           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 9.23/9.47          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.23/9.47           (k2_tops_1 @ sk_A @ sk_C)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('1', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('2', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf(redefinition_k4_subset_1, axiom,
% 9.23/9.47    (![A:$i,B:$i,C:$i]:
% 9.23/9.47     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.23/9.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.23/9.47       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 9.23/9.47  thf('3', plain,
% 9.23/9.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 9.23/9.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11))
% 9.23/9.47          | ((k4_subset_1 @ X11 @ X10 @ X12) = (k2_xboole_0 @ X10 @ X12)))),
% 9.23/9.47      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.23/9.47  thf('4', plain,
% 9.23/9.47      (![X0 : $i]:
% 9.23/9.47         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 9.23/9.47            = (k2_xboole_0 @ sk_B @ X0))
% 9.23/9.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.23/9.47      inference('sup-', [status(thm)], ['2', '3'])).
% 9.23/9.47  thf('5', plain,
% 9.23/9.47      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 9.23/9.47         = (k2_xboole_0 @ sk_B @ sk_C))),
% 9.23/9.47      inference('sup-', [status(thm)], ['1', '4'])).
% 9.23/9.47  thf('6', plain,
% 9.23/9.47      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 9.23/9.47          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.23/9.47           (k2_tops_1 @ sk_A @ sk_C)))),
% 9.23/9.47      inference('demod', [status(thm)], ['0', '5'])).
% 9.23/9.47  thf('7', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf(dt_k3_subset_1, axiom,
% 9.23/9.47    (![A:$i,B:$i]:
% 9.23/9.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.23/9.47       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.23/9.47  thf('8', plain,
% 9.23/9.47      (![X5 : $i, X6 : $i]:
% 9.23/9.47         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 9.23/9.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 9.23/9.47      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.23/9.47  thf('9', plain,
% 9.23/9.47      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 9.23/9.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('sup-', [status(thm)], ['7', '8'])).
% 9.23/9.47  thf('10', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('11', plain,
% 9.23/9.47      (![X5 : $i, X6 : $i]:
% 9.23/9.47         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 9.23/9.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 9.23/9.47      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.23/9.47  thf('12', plain,
% 9.23/9.47      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.23/9.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('sup-', [status(thm)], ['10', '11'])).
% 9.23/9.47  thf(t66_tops_1, axiom,
% 9.23/9.47    (![A:$i]:
% 9.23/9.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.23/9.47       ( ![B:$i]:
% 9.23/9.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.23/9.47           ( ![C:$i]:
% 9.23/9.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.23/9.47               ( r1_tarski @
% 9.23/9.47                 ( k2_tops_1 @
% 9.23/9.47                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 9.23/9.47                 ( k4_subset_1 @
% 9.23/9.47                   ( u1_struct_0 @ A ) @ ( k2_tops_1 @ A @ B ) @ 
% 9.23/9.47                   ( k2_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 9.23/9.47  thf('13', plain,
% 9.23/9.47      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 9.23/9.47          | (r1_tarski @ 
% 9.23/9.47             (k2_tops_1 @ X22 @ (k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X23)) @ 
% 9.23/9.47             (k4_subset_1 @ (u1_struct_0 @ X22) @ (k2_tops_1 @ X22 @ X21) @ 
% 9.23/9.47              (k2_tops_1 @ X22 @ X23)))
% 9.23/9.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 9.23/9.47          | ~ (l1_pre_topc @ X22)
% 9.23/9.47          | ~ (v2_pre_topc @ X22))),
% 9.23/9.47      inference('cnf', [status(esa)], [t66_tops_1])).
% 9.23/9.47  thf('14', plain,
% 9.23/9.47      (![X0 : $i]:
% 9.23/9.47         (~ (v2_pre_topc @ sk_A)
% 9.23/9.47          | ~ (l1_pre_topc @ sk_A)
% 9.23/9.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.23/9.47          | (r1_tarski @ 
% 9.23/9.47             (k2_tops_1 @ sk_A @ 
% 9.23/9.47              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)) @ 
% 9.23/9.47             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47              (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 9.23/9.47              (k2_tops_1 @ sk_A @ X0))))),
% 9.23/9.47      inference('sup-', [status(thm)], ['12', '13'])).
% 9.23/9.47  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('17', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf(t62_tops_1, axiom,
% 9.23/9.47    (![A:$i]:
% 9.23/9.47     ( ( l1_pre_topc @ A ) =>
% 9.23/9.47       ( ![B:$i]:
% 9.23/9.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.23/9.47           ( ( k2_tops_1 @ A @ B ) =
% 9.23/9.47             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 9.23/9.47  thf('18', plain,
% 9.23/9.47      (![X19 : $i, X20 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 9.23/9.47          | ((k2_tops_1 @ X20 @ X19)
% 9.23/9.47              = (k2_tops_1 @ X20 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19)))
% 9.23/9.47          | ~ (l1_pre_topc @ X20))),
% 9.23/9.47      inference('cnf', [status(esa)], [t62_tops_1])).
% 9.23/9.47  thf('19', plain,
% 9.23/9.47      ((~ (l1_pre_topc @ sk_A)
% 9.23/9.47        | ((k2_tops_1 @ sk_A @ sk_B)
% 9.23/9.47            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 9.23/9.47      inference('sup-', [status(thm)], ['17', '18'])).
% 9.23/9.47  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('21', plain,
% 9.23/9.47      (((k2_tops_1 @ sk_A @ sk_B)
% 9.23/9.47         = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 9.23/9.47      inference('demod', [status(thm)], ['19', '20'])).
% 9.23/9.47  thf('22', plain,
% 9.23/9.47      (![X0 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.23/9.47          | (r1_tarski @ 
% 9.23/9.47             (k2_tops_1 @ sk_A @ 
% 9.23/9.47              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)) @ 
% 9.23/9.47             (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.23/9.47              (k2_tops_1 @ sk_A @ X0))))),
% 9.23/9.47      inference('demod', [status(thm)], ['14', '15', '16', '21'])).
% 9.23/9.47  thf('23', plain,
% 9.23/9.47      ((r1_tarski @ 
% 9.23/9.47        (k2_tops_1 @ sk_A @ 
% 9.23/9.47         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.23/9.47          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))) @ 
% 9.23/9.47        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.23/9.47         (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 9.23/9.47      inference('sup-', [status(thm)], ['9', '22'])).
% 9.23/9.47  thf('24', plain,
% 9.23/9.47      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.23/9.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('sup-', [status(thm)], ['10', '11'])).
% 9.23/9.47  thf('25', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf(t32_subset_1, axiom,
% 9.23/9.47    (![A:$i,B:$i]:
% 9.23/9.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.23/9.47       ( ![C:$i]:
% 9.23/9.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.23/9.47           ( ( k7_subset_1 @ A @ B @ C ) =
% 9.23/9.47             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 9.23/9.47  thf('26', plain,
% 9.23/9.47      (![X16 : $i, X17 : $i, X18 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 9.23/9.47          | ((k7_subset_1 @ X17 @ X18 @ X16)
% 9.23/9.47              = (k9_subset_1 @ X17 @ X18 @ (k3_subset_1 @ X17 @ X16)))
% 9.23/9.47          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 9.23/9.47      inference('cnf', [status(esa)], [t32_subset_1])).
% 9.23/9.47  thf('27', plain,
% 9.23/9.47      (![X0 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.23/9.47          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 9.23/9.47              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 9.23/9.47                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 9.23/9.47      inference('sup-', [status(thm)], ['25', '26'])).
% 9.23/9.47  thf('28', plain,
% 9.23/9.47      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_C)
% 9.23/9.47         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.23/9.47            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 9.23/9.47      inference('sup-', [status(thm)], ['24', '27'])).
% 9.23/9.47  thf('29', plain,
% 9.23/9.47      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.23/9.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('sup-', [status(thm)], ['10', '11'])).
% 9.23/9.47  thf(redefinition_k7_subset_1, axiom,
% 9.23/9.47    (![A:$i,B:$i,C:$i]:
% 9.23/9.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.23/9.47       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 9.23/9.47  thf('30', plain,
% 9.23/9.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 9.23/9.47          | ((k7_subset_1 @ X14 @ X13 @ X15) = (k4_xboole_0 @ X13 @ X15)))),
% 9.23/9.47      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.23/9.47  thf('31', plain,
% 9.23/9.47      (![X0 : $i]:
% 9.23/9.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 9.23/9.47           = (k4_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0))),
% 9.23/9.47      inference('sup-', [status(thm)], ['29', '30'])).
% 9.23/9.47  thf('32', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf(d5_subset_1, axiom,
% 9.23/9.47    (![A:$i,B:$i]:
% 9.23/9.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.23/9.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.23/9.47  thf('33', plain,
% 9.23/9.47      (![X3 : $i, X4 : $i]:
% 9.23/9.47         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 9.23/9.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 9.23/9.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.23/9.47  thf('34', plain,
% 9.23/9.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 9.23/9.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 9.23/9.47      inference('sup-', [status(thm)], ['32', '33'])).
% 9.23/9.47  thf(t41_xboole_1, axiom,
% 9.23/9.47    (![A:$i,B:$i,C:$i]:
% 9.23/9.47     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 9.23/9.47       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.23/9.47  thf('35', plain,
% 9.23/9.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.23/9.47         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 9.23/9.47           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 9.23/9.47      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.23/9.47  thf('36', plain,
% 9.23/9.47      (![X0 : $i]:
% 9.23/9.47         ((k4_xboole_0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 9.23/9.47           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_B @ X0)))),
% 9.23/9.47      inference('sup+', [status(thm)], ['34', '35'])).
% 9.23/9.47  thf('37', plain,
% 9.23/9.47      (![X0 : $i]:
% 9.23/9.47         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 9.23/9.47           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_B @ X0)))),
% 9.23/9.47      inference('demod', [status(thm)], ['31', '36'])).
% 9.23/9.47  thf('38', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('39', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf(dt_k4_subset_1, axiom,
% 9.23/9.47    (![A:$i,B:$i,C:$i]:
% 9.23/9.47     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.23/9.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.23/9.47       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.23/9.47  thf('40', plain,
% 9.23/9.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 9.23/9.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 9.23/9.47          | (m1_subset_1 @ (k4_subset_1 @ X8 @ X7 @ X9) @ (k1_zfmisc_1 @ X8)))),
% 9.23/9.47      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 9.23/9.47  thf('41', plain,
% 9.23/9.47      (![X0 : $i]:
% 9.23/9.47         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 9.23/9.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.23/9.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.23/9.47      inference('sup-', [status(thm)], ['39', '40'])).
% 9.23/9.47  thf('42', plain,
% 9.23/9.47      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 9.23/9.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('sup-', [status(thm)], ['38', '41'])).
% 9.23/9.47  thf('43', plain,
% 9.23/9.47      (![X3 : $i, X4 : $i]:
% 9.23/9.47         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 9.23/9.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 9.23/9.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.23/9.47  thf('44', plain,
% 9.23/9.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 9.23/9.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47            (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 9.23/9.47      inference('sup-', [status(thm)], ['42', '43'])).
% 9.23/9.47  thf('45', plain,
% 9.23/9.47      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 9.23/9.47         = (k2_xboole_0 @ sk_B @ sk_C))),
% 9.23/9.47      inference('sup-', [status(thm)], ['1', '4'])).
% 9.23/9.47  thf('46', plain,
% 9.23/9.47      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 9.23/9.47         = (k2_xboole_0 @ sk_B @ sk_C))),
% 9.23/9.47      inference('sup-', [status(thm)], ['1', '4'])).
% 9.23/9.47  thf('47', plain,
% 9.23/9.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_B @ sk_C))
% 9.23/9.47         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 9.23/9.47      inference('demod', [status(thm)], ['44', '45', '46'])).
% 9.23/9.47  thf('48', plain,
% 9.23/9.47      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_B @ sk_C))
% 9.23/9.47         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 9.23/9.47            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 9.23/9.47      inference('demod', [status(thm)], ['28', '37', '47'])).
% 9.23/9.47  thf('49', plain,
% 9.23/9.47      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 9.23/9.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('sup-', [status(thm)], ['38', '41'])).
% 9.23/9.47  thf('50', plain,
% 9.23/9.47      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 9.23/9.47         = (k2_xboole_0 @ sk_B @ sk_C))),
% 9.23/9.47      inference('sup-', [status(thm)], ['1', '4'])).
% 9.23/9.47  thf('51', plain,
% 9.23/9.47      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 9.23/9.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('demod', [status(thm)], ['49', '50'])).
% 9.23/9.47  thf('52', plain,
% 9.23/9.47      (![X19 : $i, X20 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 9.23/9.47          | ((k2_tops_1 @ X20 @ X19)
% 9.23/9.47              = (k2_tops_1 @ X20 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19)))
% 9.23/9.47          | ~ (l1_pre_topc @ X20))),
% 9.23/9.47      inference('cnf', [status(esa)], [t62_tops_1])).
% 9.23/9.47  thf('53', plain,
% 9.23/9.47      ((~ (l1_pre_topc @ sk_A)
% 9.23/9.47        | ((k2_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 9.23/9.47            = (k2_tops_1 @ sk_A @ 
% 9.23/9.47               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.23/9.47                (k2_xboole_0 @ sk_B @ sk_C)))))),
% 9.23/9.47      inference('sup-', [status(thm)], ['51', '52'])).
% 9.23/9.47  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('55', plain,
% 9.23/9.47      (((k2_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 9.23/9.47         = (k2_tops_1 @ sk_A @ 
% 9.23/9.47            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 9.23/9.47      inference('demod', [status(thm)], ['53', '54'])).
% 9.23/9.47  thf('56', plain,
% 9.23/9.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('57', plain,
% 9.23/9.47      (![X19 : $i, X20 : $i]:
% 9.23/9.47         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 9.23/9.47          | ((k2_tops_1 @ X20 @ X19)
% 9.23/9.47              = (k2_tops_1 @ X20 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19)))
% 9.23/9.47          | ~ (l1_pre_topc @ X20))),
% 9.23/9.47      inference('cnf', [status(esa)], [t62_tops_1])).
% 9.23/9.47  thf('58', plain,
% 9.23/9.47      ((~ (l1_pre_topc @ sk_A)
% 9.23/9.47        | ((k2_tops_1 @ sk_A @ sk_C)
% 9.23/9.47            = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 9.23/9.47      inference('sup-', [status(thm)], ['56', '57'])).
% 9.23/9.47  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 9.23/9.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.23/9.47  thf('60', plain,
% 9.23/9.47      (((k2_tops_1 @ sk_A @ sk_C)
% 9.23/9.47         = (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 9.23/9.47      inference('demod', [status(thm)], ['58', '59'])).
% 9.23/9.47  thf('61', plain,
% 9.23/9.47      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) @ 
% 9.23/9.47        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.23/9.47         (k2_tops_1 @ sk_A @ sk_C)))),
% 9.23/9.47      inference('demod', [status(thm)], ['23', '48', '55', '60'])).
% 9.23/9.47  thf('62', plain, ($false), inference('demod', [status(thm)], ['6', '61'])).
% 9.23/9.47  
% 9.23/9.47  % SZS output end Refutation
% 9.23/9.47  
% 9.32/9.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
